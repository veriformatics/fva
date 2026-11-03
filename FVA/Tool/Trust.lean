import Lean
import FVA.Trust.Canary
import FVA.Trust.Collect
import FVA.Trust.Replay
import FVA.Trust.Verdict
import FVA.Tool.BaseManifest
import FVA.Tool.Sandbox

/-!
# `fva trust` (CLI glue)

`fva trust <lake-dir> [--spec-module M] [--root-module R] [--subject M]… [--paranoid]
[--surface-budget N] [--json]`: builds the project and reads its `lake env` (its search path),
both in the sandbox (`FVA.Tool.Sandbox`: the project's Lake configuration and modules are its
code), then reruns itself with that environment as `fva trust-run`, which imports the spec +
root modules, collects the facts, exports them (sandboxed) and replays them through the kernel
run set, and prints the verdict of `FVA.Trust.verdict` (proven equal to `FVA.Trust.Pass`).
rc 0 PASS, 1 FAIL, 2 usage/setup.
-/

namespace FVA.Tool.Trust

open Lean FVA.Trust

deriving instance ToJson for Proof, Claim, Flag, ReviewModule, FVA.Trust.Term, LinkKind, Link,
  Status, KernelRun, CanaryRun, Report, Issue, Verdict

/-- Parsed options. -/
structure Opts where
  dir : String := ""
  spec : Option Name := none
  root : Option Name := none
  subjects : Array Name := #[]
  paranoid : Bool := false
  budget : Option Nat := none
  json : Bool := false
  limit : Nat := 1200
  canaryLimit : Nat := 60
  canarySet : Option String := none
  known : Option String := none
  /-- `--no-sandbox` (D19): run the project's code unconfined. -/
  noSandbox : Bool := false
  /-- The sandbox mode `main` chose, for `trust-run`'s exporter (`full`, `noNet`, `off`). -/
  sandbox : String := "full"

/-- Parse options (`dir` first). -/
partial def parse (o : Opts) : List String → Except String Opts
  | [] => if o.dir.isEmpty then .error "no project directory given" else .ok o
  | "--spec-module" :: m :: r => parse { o with spec := some m.toName } r
  | "--root-module" :: m :: r => parse { o with root := some m.toName } r
  | "--subject" :: m :: r => parse { o with subjects := o.subjects.push m.toName } r
  | "--paranoid" :: r => parse { o with paranoid := true } r
  | "--no-sandbox" :: r => parse { o with noSandbox := true } r
  | "--sandbox-mode" :: m :: r => parse { o with sandbox := m } r
  | "--json" :: r => parse { o with json := true } r
  | "--surface-budget" :: n :: r => match n.toNat? with
    | some k => parse { o with budget := some k } r
    | none => .error s!"--surface-budget needs a number, got {n}"
  | "--kernel-limit" :: n :: r => match n.toNat? with
    | some k => parse { o with limit := k } r
    | none => .error s!"--kernel-limit needs a number, got {n}"
  | "--canary-set" :: f :: r => parse { o with canarySet := some f } r
  | "--known" :: f :: r => parse { o with known := some f } r
  | "--canary-limit" :: n :: r => match n.toNat? with
    | some k => parse { o with canaryLimit := k } r
    | none => .error s!"--canary-limit needs a number, got {n}"
  | a :: r =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else if o.dir.isEmpty then parse { o with dir := a } r
    else .error s!"unexpected argument {a}"

/-- Options as arguments again (for `trust-run`). -/
def Opts.args (o : Opts) : Array String :=
  #[o.dir] ++ (o.spec.map fun m => #["--spec-module", m.toString]).getD #[] ++
    (o.root.map fun m => #["--root-module", m.toString]).getD #[] ++
    o.subjects.flatMap (fun m => #["--subject", m.toString]) ++
    (if o.paranoid then #["--paranoid"] else #[]) ++
    (o.budget.map fun b => #["--surface-budget", toString b]).getD #[] ++
    (if o.json then #["--json"] else #[]) ++ #["--kernel-limit", toString o.limit] ++
    #["--canary-limit", toString o.canaryLimit] ++
    (o.canarySet.map fun f => #["--canary-set", f]).getD #[] ++
    (o.known.map fun f => #["--known", f]).getD #[] ++ #["--sandbox-mode", o.sandbox]

/-- FVA base modules: every imported module whose source is byte-identical (sha256) to the FVA
library file of the same path in `baseManifest` (compiled into this binary), except the judged
package's own (`FVA.Self.*` when judging `FVA.Self.Spec`). An edited or unknown `FVA` file is
project code and enters the review surface. -/
def baseModules (env : Environment) (judged : Name) : IO NameSet := do
  let pinned : Std.HashMap String String :=
    FVA.Tool.baseManifest.foldl (fun m (p, h) => m.insert p h) {}
  let mut cands := #[]
  for m in env.header.moduleNames do
    if judged.isPrefixOf m then continue
    let rel := "/".intercalate (m.components.map toString) ++ ".lean"
    unless pinned.contains rel do continue
    if let some f ← sourceOf m then cands := cands.push (m, rel, f)
  let shas ← sha256Of (cands.map (·.2.2))
  let mut out := {}
  for (m, rel, f) in cands do
    if shas.get? f.toString == pinned.get? rel then out := out.insert m
  return out

/-- The FVA package this binary was built in (`<pkg>/.lake/build/bin/fva`). -/
def fvaRoot : IO System.FilePath := do
  return (← IO.FS.realPath (← IO.appPath)).parent.bind (·.parent) |>.bind (·.parent)
    |>.bind (·.parent) |>.getD "."

/-- FVA's trust boundary (Decisions: Self-verification), shipped in every report. -/
def boundary : List (String × String) :=
  [("reviewed once", "FVA's specs: Wasm syntax + binary grammar, execution semantics, " ++
      "integer + IEEE-754 numerics, claim forms, certificate relations, the verdict rules " ++
      "(FVA/Spec/**)"),
   ("verified implementation", "the decoder (sound + complete for the profile), the reference " ++
      "stepper, the float operators, instantiation, the validator (validated modules never get " ++
      "stuck), the verdict function, the certificate checkers (FVA.Self: fva trust on FVA " ++
      "itself)"),
   ("trusted glue", "fact collection from the environment, the link and surface checks (a " ++
      "certificate's files included), process orchestration, the external kernels (each " ++
      "canaried)"),
   ("residual trust", "the Lean kernel cross-checked by an independent kernel, the Lean " ++
      "compiler that built fva, Mathlib at the pinned revision, the specs")]

/-- Project-derived text for the plain report: control and bidirectional-override characters
escaped, so a declaration name or file path cannot add report lines of its own. -/
def clean (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    let n := c.toNat
    if n < 0x20 || n == 0x7f || (0x202a ≤ n && n ≤ 0x202e) || (0x2066 ≤ n && n ≤ 0x2069) then
      acc ++ "\\u{" ++ String.ofList (Nat.toDigits 16 n) ++ "}"
    else acc.push c

/-- How each claim attaches to the code: `artifact` (a lifted module the claim is about),
`accepted output of R` (a certificate over blobs), `native` (a declared Lean subject); a mixed
claim lists each. -/
def attachments (env : Environment) (r : Report) : List (String × String) :=
  r.claims.map fun c =>
    let rel := match env.find? c.name.toName with
      | some (.defnInfo d) =>
        if d.value.isAppOfArity ``FVA.Cert.Accepted 3 then (d.value.getArg! 0).constName?
        else none
      | _ => none
    let kindOf (m : String) : String :=
      match r.links.find? (·.file.startsWith (m ++ " (")) with
      | some l => if l.kind == .blob then "blob" else "artifact"
      | none => "native"
    let kinds := (c.subjects.map kindOf).eraseDups
    let parts := kinds.map fun k =>
      if k == "blob" then
        s!"accepted output{(rel.map fun n => s!" of {n}").getD ""}"
      else k
    (c.name, ", ".intercalate parts)

/-- Plain report (`setFile` = the canary set used, `subjects` = the declared ones). -/
def render (r : Report) (v : Verdict) (is : List Issue) (times : List (String × Nat))
    (setFile : String) (subjects : Array Name) (attach : List (String × String) := []) :
    String :=
  Id.run do
    let mut out := s!"fva trust: {if v == .pass then "PASS" else "FAIL"}\n"
    for i in is do out := out ++ s!"  [{i.tag}] {clean i.detail}\n"
    out := out ++ "\nClaims\n"
    for c in r.claims do
      let prfs := c.proofs.map fun p => s!"{p.name} (axioms: {", ".intercalate p.axioms})"
      let how := ((attach.find? (·.1 == c.name)).map fun (_, k) => s!" ({k})").getD ""
      out := out ++ s!"  {clean c.name} — about {clean (", ".intercalate c.subjects)}{how}\n" ++
        s!"    proved by {clean ("; ".intercalate prfs)}\n"
    unless r.unmarked.isEmpty do
      out := out ++ "\nProp definitions without @[fva_claim] (not claims: nothing proves them)\n"
      for n in r.unmarked do out := out ++ s!"  {clean n}\n"
    unless subjects.isEmpty do
      out := out ++ "\nDeclared subjects (Lean-native implementations: judged, never reviewed)\n"
      for m in subjects do out := out ++ s!"  {clean m.toString}\n"
    out := out ++ "\nKernel replay\n"
    for k in r.replay do
      let ms := ((times.find? (·.1 == k.kernel)).map (·.2)).getD 0
      out := out ++ s!"  {k.kernel} ({k.lineage}): {k.status.name} ({ms / 1000} s)\n"
    out := out ++ s!"\nCanaries ({r.canarySet.length} known-false exports, {clean setFile})\n"
    for k in r.replay do
      let cs := r.canaries.filter (·.kernel == k.kernel)
      let n (s : Status) := (cs.filter (·.status == s)).length
      out := out ++ s!"  {k.kernel}: {n .reject} rejected, {n .decline} declined, " ++
        s!"{n .crash + n .timeout} crashed or timed out, {n .accept} accepted\n"
    unless r.links.isEmpty do
      out := out ++ "\nLinks\n"
      for l in r.links do
        let kind := if l.kind == .blob then "blob" else "lifted"
        out := out ++ s!"  {clean l.file} [{kind}]: {if l.ok then "matches" else "MISMATCH"}\n"
    out := out ++ s!"\nRead these: {r.surfaceLines} code lines\n"
    for m in r.reviewModules do out := out ++ s!"  {clean m.module}: {m.codeLines} lines\n"
    unless r.vocabulary.isEmpty do
      out := out ++ "\nNames the claims use from outside the project (their meaning = their docs)\n"
      for t in r.vocabulary do
        out := out ++ s!"  {t.name} ({t.origin}){if t.doc.isEmpty then "" else ": " ++ t.doc}\n"
    out := out ++ "\nWhat a PASS rests on\n"
    for (layer, what) in boundary do out := out ++ s!"  {layer}: {what}\n"
    return out

/-- The `--json` document (`fva explain` reads it), the same for every verdict. -/
def json (r : Report) (v : Verdict) (is : List Issue) (attach : List (String × String))
    (setFile knownFile : String) : Json :=
  Json.mkObj [("verdict", toJson v), ("issues", toJson is), ("report", toJson r),
    ("attachments", Json.mkObj (attach.map fun (c, k) => (c, toJson k))),
    ("canarySet", toJson setFile), ("known", toJson knownFile), ("boundary", toJson boundary)]

/-- `fva trust-run`: everything after the build, inside the project's `lake env`. The imports
run no initializer of the project (`loadExts := false`); builtin extensions such as
`implemented_by` and `extern` still read their imported entries. -/
def run (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => pure o
    | .error e => IO.eprintln s!"fva trust: {e}"; return 2
  let root ← IO.FS.realPath o.dir
  let some spec := o.spec | IO.eprintln "fva trust: --spec-module is required"; return 2
  if o.subjects.contains spec then
    IO.eprintln "fva trust: the spec module cannot be a subject (it is what a reviewer reads)"
    return 2
  let rootMod := o.root.getD spec.getPrefix
  if rootMod.isAnonymous then
    IO.eprintln "fva trust: --root-module is required for a spec module without a prefix"
    return 2
  initSearchPath (← findSysroot)
  let fvaRoot ← fvaRoot
  let trustedPkgs ← try trustedPackages root fvaRoot catch e =>
    IO.eprintln s!"fva trust: cannot read the pinned packages: {e}"; return 2
  let env ← try importModules #[{ module := spec }, { module := rootMod }] {} catch e =>
    IO.eprintln s!"fva trust: cannot import {spec} and {rootMod} (built?): {e}"; return 2
  let base ← baseModules env spec.getPrefix
  let pinFile := fvaRoot / "trust" / "oleans.tsv"
  let oleanPins ← try readOleanPins pinFile catch e =>
    IO.eprintln s!"fva trust: cannot read the .olean pins {pinFile}: {e}"; return 2
  let input : Input :=
    { root, specModule := spec, rootModule := rootMod, subjects := o.subjects, base,
      trustedPkgs, oleanPins }
  let ctx : Core.Context := { fileName := "<fva trust>", fileMap := default }
  let (r, _) ← (collect input).toIO ctx { env }
  -- replay: claims + proofs + the fixed bundle, every run-set kernel on the export
  -- + each lifted module's `decode_eq`: the fact tying `module` to the bytes is replayed by every
  -- run-set kernel even when no proof uses it
  let decls := (r.claims.map (·.name.toName) ++ r.claims.flatMap fun c =>
    c.proofs.map (·.name.toName)).toArray ++
    (liftedModules env).toArray.map (fun (_, ns) => ns ++ `decode_eq) ++
    fixedBundle.filter env.contains
  let run := kernels.filter fun k => o.paranoid || defaultKernels.contains k.name
  let (exportOk, replay, times) ← IO.FS.withTempDir fun tmp => do
    let exportPath := tmp / "export.ndjson"
    -- the exporter reads the project's `.olean`s: sandboxed, the temp dir alone writable
    let mode : Sandbox.Mode := match o.sandbox with
      | "off" => .off | "noNet" => .noNet | _ => .full
    let leanPath := (← IO.getEnv "LEAN_PATH").getD ""
    let sandbox ← if mode == .off then pure #[] else
      pure ((← Sandbox.bwrapArgs root (← findSysroot) #[tmp] mode) ++
        #["--setenv", "LEAN_PATH", leanPath])
    let exportOk ← exportDecls rootMod decls exportPath sandbox
    let mut replay := #[]
    let mut times := #[]
    if exportOk then
      -- three kernels at a time check the export side by side (memory: each loads all of it)
      let ks := run.toArray
      for b in List.range ((ks.size + 2) / 3) do
        let tasks ← (ks.extract (3 * b) (3 * b + 3)).mapM fun k => IO.asTask do
          return (k, ← runKernel k (← k.path) exportPath (tmp / s!"{k.name}.nanoda.json")
            o.limit)
        for t in tasks do
          let (k, st, ms) ← IO.ofExcept (← IO.wait t)
          replay := replay.push ({ kernel := k.name, lineage := k.lineage, status := st } :
            KernelRun)
          times := times.push (k.name, ms)
    return (exportOk, replay, times)
  -- every run-set kernel on every pinned known-false export (cached per sha256 pair)
  let setFile := (o.canarySet.map System.FilePath.mk).getD (defaultCanarySet fvaRoot)
  let pinned := (← readCanaries setFile).filter (·.bad)
  let knownFile := (o.known.map System.FilePath.mk).getD (defaultKnown fvaRoot)
  let known ← readKnown knownFile
  let canaryRuns := (← runCanaries fvaRoot run pinned o.canaryLimit 4).toList.map fun x =>
    ({ kernel := x.kernel, canary := x.canary.name, status := x.status,
       knownAccept := known.contains (x.kernel, x.canary.name) } : CanaryRun)
  let r := { r with exportOk, replay := replay.toList, budget := o.budget,
                    canaries := canaryRuns, canarySet := pinned.toList.map (·.name) }
  let is := issues r
  let v := verdict r
  let attach := attachments env r
  if o.json then IO.println (json r v is attach setFile.toString knownFile.toString).pretty
  else IO.print (render r v is times.toList s!"{setFile}; known acceptances {knownFile}" o.subjects
    attach)
  return if v == .pass then 0 else 1

/-- `fva trust-matrix [--canary-limit S]`: every bundled kernel on every pinned canary, known-false
and positive control (contract E2), as TSV: kernel, canary, kind, status, ms. -/
def matrix (argv : List String) : IO UInt32 := do
  let limit := match argv with
    | ["--canary-limit", n] => n.toNat?.getD 60
    | _ => 60
  let root ← fvaRoot
  let cs ← readCanaries (defaultCanarySet root)
  if cs.isEmpty then
    IO.eprintln "fva trust-matrix: no pinned canaries (trust/canaries/set.tsv)"; return 2
  let rs ← runCanaries root kernels cs limit 4
  IO.println "kernel\tcanary\tkind\tstatus\tms"
  for x in rs do
    IO.println (s!"{x.kernel}\t{x.canary.name}\t{if x.canary.bad then "bad" else "good"}\t" ++
      s!"{x.status.word}\t{x.ms}")
  return if rs.size == kernels.length * cs.size then 0 else 1

/-- `fva trust`: build, then `trust-run` under the project's `lake env`. -/
def main (argv : List String) : IO UInt32 := do
  let o ← match parse {} argv with
    | .ok o => if o.spec.isSome then pure o else
      IO.eprintln
        "fva trust: --spec-module is required. Run \"fva trust --help\" to see the options."
      return 2
    | .error e =>
      IO.eprintln s!"fva trust: {e}. Run \"fva trust --help\" to see the options."
      return 2
  -- `trust-run` runs inside the project: every path it gets must be absolute
  let o ← try pure { o with dir := (← IO.FS.realPath o.dir).toString } catch e =>
    IO.eprintln s!"fva trust: {e}"; return 2
  let root : System.FilePath := o.dir
  -- D23: the project's `fva.json` sets the surface budget; `--surface-budget` overrides it
  let cfg := root / "fva.json"
  let o ← if o.budget.isSome || !(← cfg.pathExists) then pure o else
    let budget := (Json.parse (← IO.FS.readFile cfg)).bind
      (·.getObjValAs? (Option Nat) "surfaceBudget")
    match budget with
    | .ok b => pure { o with budget := b }
    | .error e => IO.eprintln s!"fva trust: fva.json: {e}"; return 2
  let sysroot ← Sandbox.sysrootAt root
  -- the sandbox keeps the project root read-only: Lake cannot write a manifest there
  unless ← (root / "lake-manifest.json").pathExists do
    IO.eprintln "fva trust: the project has no lake-manifest.json (run `lake update` once)"
    return 2
  let mode ← match ← Sandbox.choose root sysroot o.noSandbox with
    | .ok m => pure m
    | .error e =>
      IO.eprintln (s!"fva trust: the sandbox for the project's code cannot start (bwrap: {e}). " ++
        "Run fva trust outside the agent's sandbox, or with --no-sandbox inside a container you " ++
        "trust")
      return 2
  unless mode == .full do IO.eprintln s!"fva trust: sandbox: {mode.describe}"
  let o := { o with
    sandbox := match mode with | .full => "full" | .noNet => "noNet" | .off => "off" }
  let b ← IO.Process.output (← Sandbox.spawnArgs root sysroot (sysroot / "bin" / "lake").toString
    #["build"] (mode := mode))
  if b.exitCode != 0 then
    let r : Report :=
      { built := false, claims := [], flags := [], reviewModules := [], subjectSyntax := [],
        unmarked := [], subjectMeaning := [],
        vocabulary := [], prelude := [], tampered := [], needsLink := false, links := [],
        exportOk := false,
        replay := [], canaries := [], canarySet := [], budget := none }
    -- D63: `--json` keeps its shape on a build failure (`fva explain` reads it)
    if o.json then IO.println (json r .fail (issues r) [] "" "").pretty
    else IO.print (render r .fail (issues r) [] "" o.subjects)
    IO.eprintln (b.stdout.takeEnd 1500).toString
    return 1
  let abs (f : Option String) : IO (Option String) :=
    f.mapM fun f => return (← IO.FS.realPath f).toString
  let o ← try pure { o with canarySet := ← abs o.canarySet, known := ← abs o.known } catch e =>
    IO.eprintln s!"fva trust: {e}"; return 2
  let some env ← Sandbox.lakeEnv root sysroot mode
    | IO.eprintln "fva trust: lake env failed"; return 2
  let self ← IO.appPath
  let child ← IO.Process.spawn
    { cmd := self.toString, args := #["trust-run"] ++ o.args, cwd := o.dir, env }
  return ← child.wait

end FVA.Tool.Trust
