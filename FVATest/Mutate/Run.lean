import FVATest.Mutate.Sites
import FVATest.Mutate.Graph
import FVATest.Mutate.Scope
import FVATest.Mutate.Config
import FVATest.Mutate.Table

/-!
# Mutation runner (contract K + R)

A run: build the primary tree, list the mutants (one `fvamut sites` process per file), key them,
reuse current rows (committed table, then local cache), and execute the rest in workers forked
from one snapshot. Per mutant the group's stages run in order; the first decisive stage wins
(K5): a Lean error inside a theorem/`example`/`#guard` or a test exiting 1 kills, an error in an
ordinary declaration makes the mutant unviable, resource diagnostics and timeouts leave it
inconclusive while independent stages continue, anything unrecognized is an `error` that fails
the run. Every digest is sha256 over the manifest + the outcome's input files (R2).
-/

namespace FVA.Mutate

open Lean System

/-- Everything a run reads once. -/
structure Ctx where
  /-- The tree under test (absolute). -/
  root : FilePath
  /-- Configuration. -/
  cfg : Config
  /-- Package module graph. -/
  graph : Graph
  /-- Declarations, Prop-valued definitions, reachability. -/
  facts : EnvFacts
  /-- sha256 of every file a digest may cover, repo-relative. -/
  hashes : Std.HashMap String String
  /-- Execution-manifest digest. -/
  manifest : String
  /-- This executable (listing subprocesses). -/
  self : FilePath
  /-- Closure of the proof roots. -/
  proofSet : NameSet
  /-- Stage override (ad-hoc runs, S4). -/
  stages? : Option (List String) := none

/-- A listed mutant in its run context. -/
structure Job where
  /-- The mutant (or probe). -/
  m : Mutant
  /-- Its scope group. -/
  group : GroupCfg
  /-- Mutant key. -/
  key : String := ""
  /-- sha256 of the id (cache file name). -/
  idHash : String := ""
  /-- sha256 (16 hex) of the mutated declaration's source text. -/
  decl : String := ""
  /-- The file's commands. -/
  cmds : Array CmdInfo
  /-- Original file text. -/
  src : String
  /-- Positive-control probe (K2). -/
  probe : Bool := false
deriving Inhabited

/-- The stages a job runs. -/
def Ctx.stagesOf (ctx : Ctx) (g : GroupCfg) : List String := ctx.stages?.getD g.stages

/-- The stages an outcome depends on, rendered with each test's argv: up to the deciding stage
(`upTo`), or all of them. -/
def Ctx.stageLine (ctx : Ctx) (g : GroupCfg) (upTo : Option String := none) : String :=
  let all := ctx.stagesOf g
  let used := match upTo with
    | some st => match all.idxOf? st with
      | some i => all.take (i + 1)
      | none => all
    | none => all
  "|".intercalate <| used.map fun s =>
    match (ctx.cfg.tests.find? fun t => s == s!"test:{t.name}") with
    | some t => s!"{s}={(toJson t.cmd).compress}" -- JSON keeps argument boundaries
    | none => s

/-- A stage's verdict. -/
inductive Res where
  | pass
  | killed (killer : String)
  | unviable (killer : String)
  | downUnviable (killer : String)
  | inconclusive (why : String)
  | error (why : String)
deriving Repr, Inhabited

/-- One-line description of a verdict. -/
def Res.show : Res → String
  | .pass => "survived"
  | .killed k => s!"killed {k}"
  | .unviable k => s!"unviable {k}"
  | .downUnviable k => s!"downstream-unviable {k}"
  | .inconclusive w => s!"inconclusive {w}"
  | .error w => s!"ERROR {w}"

/-- A located Lean diagnostic of a Lake log. -/
structure Diag where
  /-- File path as Lake prints it. -/
  file : String
  /-- Line, 1-based. -/
  line : Nat
  /-- Column, 0-based. -/
  col : Nat
  /-- Message text with its continuation lines. -/
  msg : String

/-- Located `error:` diagnostics of a Lake log, in log order, each with its continuation. -/
def diags (log : String) : Array Diag := Id.run do
  let stops := ["error:", "warning:", "info:", "trace:", "✖", "✔", "⚠", "Some required", "- "]
  let mut out : Array Diag := #[]
  let mut cur : Option Diag := none
  for l in log.splitOn "\n" do
    if stops.any (fun (p : String) => l.startsWith p) then
      if let some d := cur then out := out.push d
      cur := none
      if l.startsWith "error: " then
        match (l.drop 7).toString.splitOn ":" with
        | f :: ln :: col :: rest =>
          if f.endsWith ".lean" then
            if let (some ln, some col) := (ln.toNat?, col.trimAscii.toString.toNat?) then
              cur := some { file := f, line := ln, col, msg := ":".intercalate rest }
        | _ => pure ()
    else if let some d := cur then cur := some { d with msg := d.msg ++ "\n" ++ l }
  if let some d := cur then out := out.push d
  return out

/-- Resource exhaustion, never evidence that a proof rejects the mutant (K5). -/
def isResource (msg : String) : Bool :=
  let m := msg.toLower
  ["maximum recursion depth", "deterministic) timeout", "maximum number of heartbeats",
   "deep recursion", "stack overflow", "out of memory", "maxheartbeats", "maxrecdepth"].any
    fun p => (m.splitOn p).length > 1

/-- Lean died without a diagnostic (a runtime panic such as a `Nat.pow` exponent past a machine
word, a signal): the build is no verdict on the mutant (K5), later stages still decide. -/
def isCrash (log : String) : Bool :=
  (log.splitOn "INTERNAL PANIC").length > 1 || (log.splitOn "Lean exited with code").length > 1

/-- Original byte offset of byte `p` of the mutated text. -/
def origOffset (edits : List Edit) (p : Nat) : Nat := Id.run do
  let mut delta : Int := 0
  for e in edits do
    let s := (e.start : Int) + delta
    if (p : Int) < s then return ((p : Int) - delta).toNat
    let len : Int := e.text.utf8ByteSize
    if (p : Int) < s + len then return e.start
    delta := delta + len - ((e.stop : Int) - e.start)
  return ((p : Int) - delta).toNat

/-- Kind of the command of `cmds` holding byte `o`. -/
def kindAtOffset (cmds : Array CmdInfo) (o : Nat) : Option String :=
  (cmds.filter (·.start ≤ o)).back?.map (·.kind)

/-- Command keyword of the column-0 line opening the command around `line` (1-based), for
commands without a declaration (`example`, `#guard`). -/
def scanKind (src : String) (line : Nat) : Option String := Id.run do
  let ls := (src.splitOn "\n").toArray
  let mut i := line
  while i > 0 do
    let l := ls[i - 1]!
    if !l.isEmpty && !l.startsWith " " && !l.startsWith "--" && !l.startsWith "-/" then
      return if l.startsWith "example" then some "example"
        else if l.startsWith "#guard" then some "guard" else none
    i := i - 1
  return none

/-- Classify a diagnostic located in the mutated module (`text` = the mutated file). -/
def classifyHere (j : Job) (text : String) (d : Diag) (stage : String) : Res :=
  let loc := s!"{stage} {d.file}:{d.line}"
  if isResource d.msg then .inconclusive s!"{loc} resource" else
  let p := ((FileMap.ofString text).ofPosition ⟨d.line, d.col⟩).byteIdx
  match kindAtOffset j.cmds (origOffset j.m.edits p) with
  | some k => if ["theorem", "example", "guard"].contains k then .killed loc else .unviable loc
  | none => .error s!"unclassified diagnostic at {loc}"

/-- Classify a diagnostic located in an unchanged downstream file. -/
def classifyDown (ctx : Ctx) (d : Diag) (stage : String) : IO Res := do
  let loc := s!"{stage} {d.file}:{d.line}"
  if isResource d.msg then return .inconclusive s!"{loc} resource"
  match ctx.facts.kindAt (modOfPath d.file) d.line with
  | some ("theorem", _) => return .killed loc
  | some _ => return .downUnviable loc
  | none =>
    match scanKind (← IO.FS.readFile (ctx.root / d.file)) d.line with
    | some _ => return .killed loc
    | none => return .error s!"unclassified diagnostic at {loc}"

/-- A worker: its tree and its log directory. -/
structure Worker where
  /-- The worker's tree. -/
  dir : FilePath
  /-- Directory of the worker's stage logs. -/
  logs : FilePath
deriving Inhabited

/-- Run one stage of job `j` in worker `w` (mutated file already in place). -/
def runStage (ctx : Ctx) (w : Worker) (j : Job) (text : String) (stage : String)
    (limit : Nat) : IO Res := do
  let log := w.logs / s!"{stage.replace ":" "-"}.log"
  let mod := modOfPath j.m.file
  if stage == "module" then
    match ← runTimed w.dir ["lake", "build", s!"+{mod}"] limit log with
    | none => return .inconclusive "module timeout"
    | some 0 => return .pass
    | some _ =>
      let out ← IO.FS.readFile log
      match (diags out).find? (·.file == j.m.file) with
      | some d => return classifyHere j text d "module"
      | none => return if isCrash out then .inconclusive "module crash"
          else .error s!"module: build failed without a located error ({log})"
  else if stage == "proofs" then
    let mut failed : NameSet := {}
    let mut inconcl : Option String := none
    for p in ctx.graph.downstream mod ctx.proofSet do
      if (ctx.graph.upstream p).any failed.contains then continue
      let plog := w.logs / s!"proofs-{p}.log"
      match ← runTimed w.dir ["lake", "build", s!"+{p}"] limit plog with
      | none =>
        failed := failed.insert p
        if inconcl.isNone then inconcl := some s!"proofs {p} timeout"
      | some 0 => pure ()
      | some _ =>
        let out ← IO.FS.readFile plog
        match (diags out).find? (·.file == pathOfMod p) with
        | none =>
          unless isCrash out do
            return .error s!"proofs: {p} failed without a located error ({plog})"
          failed := failed.insert p
          if inconcl.isNone then inconcl := some s!"proofs {p} crash"
        | some d =>
          match ← classifyDown ctx d "proofs" with
          | .inconclusive why =>
            failed := failed.insert p
            if inconcl.isNone then inconcl := some why
          | r => return r
    return match inconcl with
      | some why => .inconclusive why
      | none => .pass
  else if stage == "exes" then
    match ← runTimed w.dir (["lake", "build"] ++ ctx.cfg.exes) limit log with
    | none => return .inconclusive "exes timeout"
    | some 0 => return .pass
    | some _ =>
      let out ← IO.FS.readFile log
      match (diags out)[0]? with
      | some d => classifyDown ctx d "exes"
      | none => return if isCrash out then .inconclusive "exes crash"
          else .error s!"exes: build failed without a located error ({log})"
  else
    let some t := ctx.cfg.tests.find? (s!"test:{·.name}" == stage)
      | return .error s!"unknown stage {stage}"
    match ← runTimed w.dir t.cmd limit log with
    | none => return .inconclusive s!"{stage} timeout"
    | some 0 => return .pass
    | some 1 => return .killed stage
    | some 3 => return .inconclusive s!"{stage} crash"
    | some rc => return .error s!"{stage}: rc {rc} (infrastructure, {log})"

/-- Content listing (sha256 + path) of a worker tree, minus the build directory and the shared
paths: a stray write of any size shows. -/
def treeListing (ctx : Ctx) (dir : FilePath) : IO String := do
  let prunes := " ".intercalate <| (".lake/build" :: ctx.cfg.shared).map fun p =>
    s!"-path './{p}' -prune -o"
  runOk "bash" #["-c", s!"find . {prunes} -type f -print0 | sort -z | xargs -0 -r sha256sum"] dir

/-- Sorted (path, size) listing of a build directory. -/
def buildListing (dir : FilePath) : IO String := do
  let s ← runOk "find" #[".lake/build", "-type", "f", "-printf", "%P %s\\n"] dir
  return "\n".intercalate (((s.splitOn "\n").toArray.qsort (· < ·)).toList)

/-- Restore `w/.lake/build` to the snapshot's: files changed since `stamp` (by ctime, which no
writer can preserve, unlike `cp -p`'s mtime) come back from the snapshot (or go, when the
snapshot lacks them); a listing mismatch falls back to a full copy. A full copy per mutant would
move 0.4 GB each time where reflinks are unavailable. -/
def resetBuild (snap : FilePath) (w : Worker) (stamp : FilePath) (snapBuild : String) :
    IO Unit := do
  discard <| runOk "bash" #["-c",
    "cd \"$0\" && find .lake/build -cnewer \"$1\" \\( -type f -o -type l \\) -print0 | " ++
    "while IFS= read -r -d '' f; do if [[ -e $2/$f ]]; then " ++
    "cp -a --reflink=auto \"$2/$f\" \"$f\"; else rm -f \"$f\"; fi; done",
    w.dir.toString, stamp.toString, snap.toString]
  if (← buildListing w.dir) != snapBuild then
    copyTree (snap / ".lake" / "build") (w.dir / ".lake" / "build")

/-- Run job `j`'s stages in `w`; restore the worker afterwards. Returns the verdict and the
wall-clock of each stage (ms). -/
def pipeline (ctx : Ctx) (snap : FilePath) (snapList snapBuild : String) (w : Worker) (j : Job)
    (limits : String → Nat) : IO (Res × Array (String × Nat)) := do
  let text := j.m.apply j.src
  let stamp := w.logs / "stamp"
  IO.FS.writeFile stamp ""
  IO.FS.writeFile (w.dir / j.m.file) text
  let mut times := #[]
  let mut inconcl : Option String := none
  let mut skipTests := false
  let mut verdict : Option Res := none
  for st in ctx.stagesOf j.group do
    if skipTests && st.startsWith "test:" then continue
    let t0 ← IO.monoMsNow
    let r ← runStage ctx w j text st (limits st)
    times := times.push (st, (← IO.monoMsNow) - t0)
    match r with
    | .pass => pure ()
    | .inconclusive why =>
      if inconcl.isNone then inconcl := some why
      if st == "module" then break
      if st == "exes" then skipTests := true
    | r => verdict := some r; break
  IO.FS.writeFile (w.dir / j.m.file) j.src
  resetBuild snap w stamp snapBuild
  if (← treeListing ctx w.dir) != snapList then
    copyTree snap w.dir -- later mutants on this worker start clean
    return (.error s!"worker {w.dir} changed outside its build directory", times)
  let r := verdict.getD (match inconcl with
    | some why => .inconclusive why
    | none => .pass)
  return (r, times)

/-- Repo-relative files of a test's inputs: its executables' closures + its declared files. -/
def Ctx.testInputs (ctx : Ctx) (t : TestCfg) (expand : List String → Array String) :
    Array String :=
  (t.exeRoots.toArray.flatMap fun r => (ctx.graph.upstream r.toName).map pathOfMod) ++
    expand t.files

end FVA.Mutate
