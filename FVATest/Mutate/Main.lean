import FVATest.Mutate.Run

/-!
# `fvamut` — mutation check driver (contract `docs/contracts/U12-mutation.md`)

`fvamut [check|update|fresh|list] [--config F] [--files F…] [--decls D…] [--stages S…]
[--workers N] [--spot N]`, run from the tree root under `lake env` (the facts import needs the
package's search path). `check` (full gate) never writes; `update` runs the stale mutants and
rewrites the results table; `fresh` reruns every mutant ignoring both caches; `list` prints the
mutants.
Ad-hoc selections (`--files`, `--decls`, `--stages`) report without touching the table.
rc 0 = clean, 1 = findings (stale, unruled, conflict, spot-check mismatch, error), 2 = setup.
`fvamut sites <file> [--keep F | --skip F]` = one file's JSON listing (internal).
-/

open Lean System FVA.Mutate

/-- `sites` subcommand: list one file (fresh process: one `importModules` each). -/
unsafe def sitesMain (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let names (f : String) : IO NameSet := do
    return (← IO.FS.lines f).foldl (fun s l => s.insert l.toName) {}
  let listing ← match args with
    | [file] => listFile file fun _ => true
    | [file, "--keep", f] => do let s ← names f; listFile file s.contains
    | [file, "--skip", f] => do let s ← names f; listFile file (!s.contains ·)
    | _ => throw <| IO.userError "usage: fvamut sites <file> [--keep F | --skip F]"
  IO.println (toJson listing).compress
  return 0

/-- Command-line options of a run. -/
structure Opts where
  mode : String := "check"
  config : String := "FVATest/Mutate/config.json"
  files : List String := []
  decls : List String := []
  stages : Option (List String) := none
  workers : Option Nat := none
  spot : Option Nat := none

/-- Parse run options. -/
partial def parseOpts (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | m :: rest =>
    if ["check", "update", "fresh", "list"].contains m then parseOpts { o with mode := m } rest
    else if m == "--config" then match rest with
      | f :: r => parseOpts { o with config := f } r
      | [] => .error "--config needs a file"
    else if m == "--workers" || m == "--spot" then match rest with
      | n :: r => match n.toNat? with
        | some k =>
          if m == "--workers" && k == 0 then .error "--workers needs at least 1"
          else parseOpts (if m == "--spot" then { o with spot := some k }
            else { o with workers := some k }) r
        | none => .error s!"{m} needs a number"
      | [] => .error s!"{m} needs a number"
    else if ["--files", "--decls", "--stages"].contains m then
      let (vals, r) := rest.span (!·.startsWith "--")
      let o := if m == "--files" then { o with files := vals }
        else if m == "--decls" then { o with decls := vals } else { o with stages := some vals }
      parseOpts o r
    else .error s!"unknown argument {m}"

/-- Every file under the given paths (directories expanded), repo-relative, sorted. -/
def expandFiles (root : FilePath) (paths : List String) : IO (Array String) := do
  let mut out := #[]
  for p in paths do
    let fp := root / p
    if ← fp.isDir then
      for e in ← fp.walkDir do
        unless ← e.isDir do out := out.push (e.toString.drop (root.toString.length + 1)).toString
    else if ← fp.pathExists then out := out.push p
  return out.qsort (· < ·)

/-- Listing of one file through a `sites` subprocess. -/
def listVia (self root : FilePath) (file : String) (filter : Option (String × Array Name)) :
    IO Listing := do
  let mut args := #["sites", file]
  if let some (flag, names) := filter then
    let tmp := root / ".cache" / "mutate" / "names" / s!"{(file.replace "/" "_")}.txt"
    IO.FS.createDirAll (tmp.parent.getD ".")
    IO.FS.writeFile tmp ("\n".intercalate (names.map toString).toList ++ "\n")
    args := args ++ #[flag, tmp.toString]
  let out ← runOk self.toString args root
  IO.ofExcept (Json.parse out >>= fromJson?)

/-- Mutants of every scope group (S1), with each file's listing. -/
def listAll (ctx : Ctx) (opts : Opts) : IO (Array Job × Array (String × Listing)) := do
  let cfg := ctx.cfg
  let filesOf (g : GroupCfg) : IO (Array String) := do
    let fs ← leanFiles ctx.root g.dirs
    return fs.filter fun f => !cfg.exclude.any (f.startsWith ·)
  let mut plan : Array (GroupCfg × String × Option (String × Array Name)) := #[]
  for g in cfg.groups do
    if g.reachFrom.isEmpty then
      for f in ← filesOf g do
        let m := modOfPath f
        let skip := ctx.facts.propDefs.toArray.filter fun c => ctx.facts.moduleOf.get? c == some m
        plan := plan.push (g, f, some ("--skip", skip))
    else
      let mut roots : NameSet := {}
      for gname in g.reachFrom do
        if let some src := cfg.groups.find? (·.name == gname) then
          for f in ← filesOf src do roots := roots.insert (modOfPath f)
      let reached := ctx.facts.reach roots fun m => g.within.toName.isPrefixOf m
      let byFile := reached.toArray.foldl (fun (acc : Std.HashMap String (Array Name)) c =>
        match ctx.facts.moduleOf.get? c with
        | some m => acc.insert (pathOfMod m) ((acc.getD (pathOfMod m) #[]).push c)
        | none => acc) {}
      for (f, names) in byFile.toArray.qsort (·.1 < ·.1) do
        plan := plan.push (g, f, some ("--keep", names))
  let chosen := plan.filter fun (_, f, _) => opts.files.isEmpty || opts.files.contains f
  let tasks ← chosen.mapM fun (g, f, flt) =>
    IO.asTask (prio := .dedicated) (do return (g, f, ← listVia ctx.self ctx.root f flt))
  let mut jobs := #[]
  let mut listings := #[]
  for t in tasks do
    let (g, f, l) ← IO.ofExcept (← IO.wait t)
    unless l.errors.isEmpty do
      throw <| IO.userError s!"{f} does not elaborate cleanly: {l.errors.take 3}"
    let src ← IO.FS.readFile (ctx.root / f)
    listings := listings.push (f, l)
    for m in l.mutants do
      if opts.decls.isEmpty || opts.decls.contains m.decl then
        jobs := jobs.push { m, group := g, cmds := l.commands, src }
  return (jobs, listings)

/-- Source text of the command declaring `decl`. -/
def declText (j : Job) : String :=
  match j.cmds.find? (·.names.contains j.m.decl) with
  | some c => slice j.src c.start c.stop
  | none => ""

/-- Fill each job's key, id hash and declaration digest (one `sha256sum` batch). -/
def keyJobs (ctx : Ctx) (tmp : FilePath) (jobs : Array Job) : IO (Array Job) := do
  let keyStr (j : Job) := s!"{ctx.hashes.getD j.m.file "missing"}\n{(toJson j.m.edits).compress}"
  let strs := jobs.flatMap fun j => #[keyStr j, j.m.id, declText j]
  let hs ← sha256Strings tmp strs
  return jobs.mapIdx fun i j =>
    { j with
      key := hs[3 * i]!, idHash := hs[3 * i + 1]!, decl := (hs[3 * i + 2]!.take 16).toString }

/-- Inputs of an outcome (R2): `all`, `up:<module>` or `test:<name>`. -/
def depKey (j : Job) (outcome killer : String) : String :=
  if needsRuling outcome then "all"
  else if killer.startsWith "test:" then killer
  else match (killer.splitOn " ").getD 1 "" |>.splitOn ":" with
    | f :: _ => if f.endsWith ".lean" then s!"up:{modOfPath f}" else "all"
    | [] => s!"up:{modOfPath j.m.file}"

/-- Files of a dependency key. -/
def depFiles (ctx : Ctx) (expand : List String → Array String) (key : String) : Array String :=
  if key.startsWith "up:" then (ctx.graph.upstream (key.drop 3).toString.toName).map pathOfMod
  else if key.startsWith "test:" then
    match ctx.cfg.tests.find? (s!"test:{·.name}" == key) with
    | some t => ctx.testInputs t expand
    | none => #[]
  else
    ctx.graph.mods.map pathOfMod ++ ctx.cfg.tests.toArray.flatMap (ctx.testInputs · expand)

/-- Memoized dependency digests by (stage line, dependency key). -/
structure Digests where
  memo : Std.HashMap String String := {}

/-- Dependency digest of an outcome of `j`. -/
def digestFor (ctx : Ctx) (expand : List String → Array String) (tmp : FilePath)
    (d : IO.Ref Digests) (j : Job) (outcome killer : String) : IO String := do
  let k := depKey j outcome killer
  let deciding := if needsRuling outcome then none else (killer.splitOn " ").head?
  let memoKey := s!"{ctx.stageLine j.group deciding}\n{k}"
  if let some v := (← d.get).memo.get? memoKey then return v
  let files := (depFiles ctx expand k).qsort (· < ·)
  let body := "\n".intercalate (files.map fun f => s!"{ctx.hashes.getD f "missing"} {f}").toList
  let v := (← sha256Strings tmp #[s!"{ctx.manifest}\n{memoKey}\n{body}"])[0]!
  d.modify fun s => { s with memo := s.memo.insert memoKey v }
  return v

/-- Row of a finished job. -/
def rowOf (ctx : Ctx) (expand : List String → Array String) (tmp : FilePath) (d : IO.Ref Digests)
    (j : Job) (r : Res) : IO (Option Row) := do
  let (outcome, killer) := match r with
    | .pass => ("survived", "-")
    | .killed k => ("killed", k)
    | .unviable k => ("unviable", k)
    | .downUnviable k => ("downstream-unviable", k)
    | .inconclusive w => ("inconclusive", w)
    | .error _ => ("error", "")
  if outcome == "error" then return none
  let deps ← digestFor ctx expand tmp d j outcome killer
  return some { id := j.m.id, key := j.key, outcome, killer, deps }

/-- Shared read-only inputs: sorted listing (path, size, mtime) of every file under them. -/
def sharedListing (root : FilePath) (paths : List String) : IO String := do
  let present ← paths.filterM fun (p : String) => (root / p).pathExists
  if present.isEmpty then return ""
  runOk "bash" (#["-c", "find -L \"$@\" -type f -printf '%p %s %T@\\n' | sort", "_"] ++
    present.toArray) root

/-- Fork the snapshot (K1): tracked + untracked-unignored files, the build, shared symlinks. -/
def makeSnapshot (ctx : Ctx) (snap : FilePath) : IO Unit := do
  if ← snap.pathExists then discard <| runOk "rm" #["-rf", snap.toString]
  IO.FS.createDirAll snap
  -- the working tree as it is: tracked files deleted on disk stay out
  discard <| runOk "bash" #["-c",
    "git ls-files -co --exclude-standard -z | while IFS= read -r -d '' f; do " ++
      "[[ -e $f ]] && printf '%s\\0' \"$f\"; done | xargs -0 -r cp --parents -t \"$0\"",
    snap.toString] ctx.root
  IO.FS.createDirAll (snap / ".lake")
  for d in ["build", "config"] do
    if ← (ctx.root / ".lake" / d).pathExists then
      copyTree (ctx.root / ".lake" / d) (snap / ".lake" / d)
  for p in ctx.cfg.shared do
    if ← (ctx.root / p).pathExists then
      IO.FS.createDirAll ((snap / p).parent.getD snap)
      discard <| runOk "ln" #["-sfn", (ctx.root / p).toString, (snap / p).toString]

/-- Positive-control probe of module file `f` (K2): a fresh unused definition at the end. -/
def probeJob (j : Job) : Job :=
  let txt := "\n/-- fvamut probe (U12 K2): unused; changes the module's olean. -/\n" ++
    "def fvamutProbe : Nat := 0\n"
  let n := j.src.utf8ByteSize
  { j with
    m := { j.m with decl := "probe", op := "PROBE", k := 0, edits := [⟨n, n, txt⟩],
                    orig := "", repl := "probe" }
    probe := true }

/-- Stage limit from a probe's wall-clock (K6). -/
def limitFrom (floor : Nat) (times : Array (String × Nat)) (factor : Nat) (st : String) : Nat :=
  let ms := ((times.find? (·.1 == st)).map (·.2)).getD 12000
  factor * max floor (5 * ((ms + 999) / 1000))

/-- Run `jobs` on `workers` (static partition); returns each job's verdict. `record` runs as
each job finishes (the local cache keeps finished work when a run is interrupted). -/
def runJobs (ctx : Ctx) (snap : FilePath) (snapList snapBuild : String) (workers : Array Worker)
    (jobs : Array Job) (limits : Job → String → Nat) (progress : IO.Ref Nat) (total : Nat)
    (record : Job → Res → IO Unit := fun _ _ => pure ()) :
    IO (Array (Job × Res × Array (String × Nat))) := do
  let n := workers.size
  let tasks ← workers.mapIdxM fun wi w => IO.asTask (prio := .dedicated) do
    let mut out := #[]
    let mut i := wi
    while i < jobs.size do
      let j := jobs[i]!
      let t0 ← IO.monoMsNow
      let (r, times) ← pipeline ctx snap snapList snapBuild w j (limits j)
      record j r
      let k ← progress.modifyGet fun c => (c + 1, c + 1)
      IO.println s!"fvamut: [{k}/{total}] {j.m.id} → {r.show} ({((← IO.monoMsNow) - t0) / 1000} s)"
      (← IO.getStdout).flush
      out := out.push (j, r, times)
      i := i + n
    return out
  let mut all := #[]
  for t in tasks do all := all ++ (← IO.ofExcept (← IO.wait t))
  return all

/-- The runner's identity, the same on every host: sha256 of its sources (`FVATest/Mutate/*.lean`
of the tree that built `.lake/build/bin/fvamut`); the binary's own hash when they are absent.
Binary bytes and host tools (`jq`, `bash`) stay out: a committed row must stay current on CI
and on every pool host. -/
def runnerId (self : FilePath) : IO String := do
  let repo := ((self.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)
  let srcs ← match repo with
    | some r => do
      let fs ← expandFiles r ["FVATest/Mutate"]
      pure (r, fs.filter fun f => f.endsWith ".lean" && !f.startsWith "FVATest/Mutate/fixture")
    | none => pure (".", #[])
  if srcs.2.isEmpty then return ((← runOk "sha256sum" #[self.toString]).take 64).toString
  let hs ← sha256Files srcs.1 srcs.2
  return "\n".intercalate (srcs.2.map fun f => s!"{hs.getD f ""} {f}").toList

/-- Value of a lowercase hex string. -/
def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + if c.isDigit then c.toNat - 48 else c.toNat - 87) 0

/-- Seeded selection of `k` distinct indices below `n`. -/
def pick (seed n k : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut x := seed % 2147483647 + 1
  let mut tries := 0
  while out.size < min k n && tries < 1000 do
    x := (x * 48271) % 2147483647
    let i := x % n
    unless out.contains i do out := out.push i
    tries := tries + 1
  return out

/-- The run. -/
def runMain (opts : Opts) : IO UInt32 := do
  let root ← IO.currentDir
  let cfg ← Config.load (root / opts.config)
  let self ← IO.appPath
  let cache := root / cfg.cacheDir
  let tmp := cache / "tmp"
  -- primary build (the tree must check clean before any mutant, K1)
  let b ← run "lake" ((#["build"] ++ cfg.proofRoots.toArray) ++ cfg.exes.toArray) root
  if b.exitCode != 0 then
    IO.eprintln s!"fvamut: the unmutated tree does not build:\n{b.stdout.takeEnd 2000}"
    return 2
  let graph ← Graph.build root cfg.srcRoots cfg.exclude
  let pkg : NameSet := graph.mods.foldl (·.insert ·) {}
  let factMods := graph.mods.filter fun m => !cfg.exeRoots.contains m.toString
  let facts ← loadFacts factMods pkg
  let testFiles ← expandFiles root (cfg.tests.flatMap (·.files))
  let hashFiles := (graph.mods.map pathOfMod ++ testFiles ++ cfg.keyFiles.toArray ++
    cfg.tools.toArray).filter (!·.isEmpty)
  let present ← hashFiles.filterM fun (f : String) => (root / f).pathExists
  let hashes ← sha256Files root present
  let versions ← cfg.versions.mapM fun argv => do
    match argv with
    | c :: args => return (← run c args.toArray).stdout.trimAscii.toString
    | [] => return ""
  -- configuration minus what enters per-group stage lines (stages, test argv) or never changes
  -- an outcome (workers, spot-check count, the paths of the generated files)
  let core : Config :=
    { cfg with
      groups := cfg.groups.map fun g => { g with stages := [] }
      tests := cfg.tests.map fun t => { t with cmd := [] }
      workers := 0, spotChecks := 0, results := "", rulings := "" }
  let cfgCore := toJson core
  let manifestBody := "\n".intercalate <|
    ((cfg.keyFiles.toArray ++ cfg.tools.toArray).map
      fun f => s!"{hashes.getD f "missing"} {f}").toList ++ versions ++
      [s!"runner {← runnerId self}", cfgCore.compress]
  let manifest := (← sha256Strings tmp #[manifestBody])[0]!
  -- a test's declared directories expand to their files for every digest
  let expandT := fun (ps : List String) =>
    testFiles.filter fun f => ps.any fun p => f == p || f.startsWith (p ++ "/")
  let proofSet := graph.closure (cfg.proofRoots.toArray.map (·.toName))
  let ctx : Ctx := { root, cfg, graph, facts, hashes, manifest, self, proofSet,
                     stages? := opts.stages }
  let (jobs, listings) ← listAll ctx opts
  let jobs ← keyJobs ctx tmp jobs
  -- inventory (S3)
  let mut inv := #[]
  for (f, l) in listings do
    for d in l.decls do
      inv := inv.push s!"{f}\t{d.name}\t{d.kind}\t{d.sites.map toString |>.getD "excluded"}"
  IO.FS.createDirAll cache
  IO.FS.writeFile (cache / "inventory.tsv") ("\n".intercalate inv.toList ++ "\n")
  let zeroSite := (listings.flatMap fun (_, l) => l.decls).filter (·.sites == some 0)
  if opts.mode == "list" then
    for j in jobs do IO.println s!"{j.m.id}\tline {j.m.line}\t{snippetOf j.m.orig j.m.repl}"
    IO.println s!"fvamut: {jobs.size} mutants"
    return 0
  let adhoc := !opts.files.isEmpty || !opts.decls.isEmpty || opts.stages.isSome
  -- reuse current rows
  let digests ← IO.mkRef ({} : Digests)
  let tableRows ← readTable (root / cfg.results)
  let mut findings : Array String := #[]
  if tableRows.any (·.isNone) then findings := findings.push "results table has malformed lines"
  let table := tableRows.filterMap id
  let mut byId : Std.HashMap String Row := {}
  for r in table do
    if byId.contains r.id then findings := findings.push s!"duplicate row {r.id}"
    byId := byId.insert r.id r
  let current (j : Job) (r : Row) : IO Bool := do
    return r.key == j.key && r.deps == (← digestFor ctx expandT tmp digests j r.outcome r.killer)
  let fresh := opts.mode == "fresh"
  let mut rows : Std.HashMap String Row := {}
  let mut stale : Array Job := #[]
  let mut fromTable := 0
  let mut fromCache := 0
  for j in jobs do
    let tab := if fresh then none else byId.get? j.m.id
    let tabOk ← match tab with
      | some r => current j r
      | none => pure false
    if tabOk then
      rows := rows.insert j.m.id tab.get!
      fromTable := fromTable + 1
      -- a current committed row contradicted by a recorded execution (G1)
      if let some c ← readCache cache j.idHash j.key then
        if c.deps == tab.get!.deps && (c.outcome != tab.get!.outcome || c.killer != tab.get!.killer)
        then findings := findings.push <| s!"cache conflict {j.m.id}: table " ++
          s!"{tab.get!.outcome} {tab.get!.killer}, cache {c.outcome} {c.killer}"
      continue
    let cached ← if fresh then pure none else readCache cache j.idHash j.key
    match cached with
    | some c =>
      if ← current j c then
        rows := rows.insert j.m.id c
        fromCache := fromCache + 1
        continue
    | none => pure ()
    stale := stale.push j
  let jobIds : Std.HashSet String := jobs.foldl (·.insert ·.m.id) {}
  let extra := if adhoc then #[] else table.filter fun r => !jobIds.contains r.id
  -- execute (update/fresh), or spot-check (check)
  let needRun := opts.mode != "check" && !stale.isEmpty
  let spot : Array Job := if opts.mode == "check" && !adhoc && stale.isEmpty then
      let seed := ((hashes.toArray.filter (·.1 != cfg.results)).qsort (·.1 < ·.1)).foldl
        (fun acc (_, h) => (acc * 31 + hexVal (h.take 12).toString) % 1000000007) 7
      (pick seed jobs.size (opts.spot.getD cfg.spotChecks)).map (jobs[·]!)
    else #[]
  if needRun || !spot.isEmpty then
    let cores := (← run "nproc" #[]).stdout.trimAscii.toString.toNat!
    let nw := opts.workers.getD (if cfg.workers > 0 then cfg.workers else max 1 (cores / 2))
    let runDir := cache / "run"
    let snap := runDir / "snap"
    makeSnapshot ctx snap
    let snapList ← treeListing ctx snap
    let snapBuild ← buildListing snap
    let workers ← (Array.range nw).mapM fun i => do
      let w : Worker := { dir := runDir / s!"w{i}", logs := runDir / "logs" / s!"w{i}" }
      copyTree snap w.dir
      IO.FS.createDirAll w.logs
      return w
    let sharedBefore ← sharedListing root cfg.shared
    let progress ← IO.mkRef 0
    if needRun then
      -- probes (K2): one per module with stale mutants
      let mods := stale.foldl (fun (acc : Array Job) j =>
        if acc.any (·.m.file == j.m.file) then acc else acc.push j) #[]
      let probes := mods.map probeJob
      IO.println s!"fvamut: {stale.size} stale mutants in {probes.size} modules, {nw} workers"
      let probeRes ← runJobs ctx snap snapList snapBuild workers probes (fun _ _ => 3600) progress
        probes.size
      let mut times : Std.HashMap String (Array (String × Nat)) := {}
      for (j, r, t) in probeRes do
        match r with
        | .pass => times := times.insert j.m.file t
        | _ =>
          IO.eprintln <| s!"fvamut: probe of {j.m.file} did not survive ({r.show}): " ++
            "the unmutated pipeline fails, nothing is classified"
          return 2
      progress.set 0
      let limits := fun (factor : Nat) (j : Job) (st : String) =>
        limitFrom cfg.minLimit (times.getD j.m.file #[]) factor st
      -- finished executions go to the local cache at once; timeouts + crashes wait for the solo
      -- rerun, errors never get a row
      let record := fun (j : Job) (r : Res) => do
        let pending := match r with
          | .inconclusive w => w.endsWith "timeout" || w.endsWith "crash"
          | _ => false
        unless pending do
          if let some row ← rowOf ctx expandT tmp (← IO.mkRef ({} : Digests)) j r then
            writeCache cache j.idHash row
      let res ← runJobs ctx snap snapList snapBuild workers stale (limits 1) progress stale.size
        record
      -- timeouts and crashes rerun alone at 3 × the limit (K6)
      let (solo, done) := res.partition fun (_, r, _) => match r with
        | .inconclusive w => w.endsWith "timeout" || w.endsWith "crash"
        | _ => false
      let soloRes ← if solo.isEmpty then pure #[] else do
        IO.println s!"fvamut: {solo.size} timeouts/crashes rerun alone"
        progress.set 0
        runJobs ctx snap snapList snapBuild #[workers[0]!] (solo.map (·.1)) (limits 3) progress
          solo.size
      for (j, r, _) in done ++ soloRes do
        match ← rowOf ctx expandT tmp digests j r with
        | some row =>
          writeCache cache j.idHash row
          rows := rows.insert j.m.id row
        | none => findings := findings.push s!"error {j.m.id}: {r.show}"
    let spotRes ← if spot.isEmpty then pure #[] else
      runJobs ctx snap snapList snapBuild workers spot (fun _ _ => 1200) progress spot.size
    for (j, r, _) in spotRes do
      let some row := rows.get? j.m.id | continue
      match ← rowOf ctx expandT tmp digests j r with
      | some fr =>
        if fr.outcome != row.outcome || fr.killer != row.killer then
          findings := findings.push <| s!"spot-check {j.m.id}: table {row.outcome} " ++
            s!"{row.killer}, rerun {fr.outcome} {fr.killer}"
        else IO.println s!"fvamut: spot-check {j.m.id} reproduced ({row.outcome} {row.killer})"
      | none => findings := findings.push s!"spot-check {j.m.id}: {r.show}"
    if (← sharedListing root cfg.shared) != sharedBefore then
      findings := findings.push s!"shared inputs changed during the run: {cfg.shared}"
  -- table
  let missing := jobs.filter fun j => !rows.contains j.m.id
  if opts.mode != "check" && !adhoc && missing.isEmpty then
    writeTable (root / cfg.results) (jobs.filterMap fun j => rows.get? j.m.id)
  if opts.mode == "check" && adhoc && !stale.isEmpty then
    findings := findings.push <| s!"{stale.size} selected mutants without a current row " ++
      "(run scripts/test-mutation update with the same selection)"
  if opts.mode != "check" && !missing.isEmpty then
    findings := findings.push s!"{missing.size} mutants without a result (run incomplete)"
  if opts.mode == "check" && !adhoc && (!stale.isEmpty || !extra.isEmpty || fromCache > 0) then
    findings := findings.push <| s!"{cfg.results} stale: {stale.size + fromCache} mutants " ++
      s!"without a current row ({fromCache} current only in {cfg.cacheDir}), {extra.size} rows " ++
      "without a mutant (run scripts/test-mutation --update)"
  -- rulings (L1–L2)
  let (rulings, badRulings) ← readRulings (root / cfg.rulings)
  findings := findings ++ badRulings
  let needs := jobs.filter fun j => match rows.get? j.m.id with
    | some r => needsRuling r.outcome
    | none => false
  let mut unruled := #[]
  for j in needs do
    match rulings.find? (·.id == j.m.id) with
    | none => unruled := unruled.push j.m.id
    | some ru =>
      let snip := snippetOf j.m.orig j.m.repl
      let contractOk ← match ru.contract.splitOn "@" with
        | [path, h] => do
          let hs ← sha256Files root #[path]
          pure ((hs.getD path "").take 16 == h)
        | _ => pure (ru.contract == "-" && ru.verdict != "unspecified")
      -- `resource` rules an inconclusive row alone; `unspecified` names its contract clause
      let outcome := ((rows.get? j.m.id).map (·.outcome)).getD ""
      unless ru.verdict != "resource" || outcome == "inconclusive" do
        findings := findings.push s!"ruling {j.m.id}: verdict resource on a {outcome} row"
      unless ru.snippet == snip && ru.decl == j.decl && contractOk do
        findings := findings.push
          s!"stale ruling {j.m.id} (snippet, declaration or contract changed)"
  let needIds : Std.HashSet String := needs.foldl (·.insert ·.m.id) {}
  for ru in rulings do
    unless needIds.contains ru.id || adhoc do
      findings := findings.push s!"stale ruling {ru.id}: no current survived/inconclusive row"
  unless unruled.isEmpty do
    findings := findings.push
      s!"{unruled.size} unruled survived/inconclusive mutants: {unruled.toList.take 20}"
    -- ruling templates (L1): verdict, contract, reviewer + reason left for the reviewer
    let todo := (needs.filter fun j => unruled.contains j.m.id).map fun j =>
      s!"{j.m.id}\t{snippetOf j.m.orig j.m.repl}\t?\t{j.decl}\t-\t?\t" ++
        s!"{(rows.get? j.m.id).map (fun r => s!"{r.outcome} {r.killer}") |>.getD ""}"
    IO.FS.writeFile (cache / "rulings-todo.tsv") ("\n".intercalate todo.toList ++ "\n")
  -- report
  let count (o : String) := (jobs.filter fun j => (rows.get? j.m.id).any (·.outcome == o)).size
  IO.println <| s!"fvamut: {jobs.size} mutants ({fromTable} table rows, {fromCache} cache, " ++
    s!"{jobs.size - fromTable - fromCache} run or pending); killed {count "killed"}, " ++
    s!"unviable {count "unviable"}, downstream-unviable {count "downstream-unviable"}, " ++
    s!"survived {count "survived"}, inconclusive {count "inconclusive"}; " ++
    s!"{needs.size - unruled.size} ruled; {zeroSite.size} zero-site declarations " ++
    s!"(inventory: {cfg.cacheDir}/inventory.tsv)"
  for f in findings do IO.println s!"fvamut: FINDING {f}"
  unless unruled.isEmpty do
    IO.println s!"fvamut: ruling templates for the unruled rows: {cfg.cacheDir}/rulings-todo.tsv"
  return if findings.isEmpty then 0 else 1

/-- Entry point. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | "sites" :: rest => sitesMain rest
  | _ =>
    match parseOpts {} args with
    | .error e => IO.eprintln s!"fvamut: {e}"; return 2
    | .ok o =>
      initSearchPath (← findSysroot)
      enableInitializersExecution
      try runMain o catch e => IO.eprintln s!"fvamut: {e}"; return 2
