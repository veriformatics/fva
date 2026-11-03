import Lean
import FVA.Trust.Olean

/-!
# Project `.olean`s tied to their sources (D65, trusted glue)

The project's sandboxed build writes its own `.olean`s, and its Lake configuration can rewrite one
after elaboration (a build target), so the meaning trust-run imports and the kernels replay can
differ from the source the reviewer reads. FVA compiles every project and subject module of the
spec module's import closure itself, in the same sandbox, and the compiled files must be equal.
Each import such a module reads is Lean core, Mathlib or FVA base (byte-pinned, D48 + D49) or
another module checked here, so an equal closure is the build of its sources. Modules that only
the proofs import stay out: their terms reach the verdict through kernel replay against the claim
types, and a proof module cannot redeclare a spec constant.
-/

namespace FVA.Trust

open Lean System

/-- The setup FVA compiles `m` with: `package`, `isModule` and `options` from Lake's setup file
beside the build (`…/.lake/build/ir/<module path>.setup.json`; defaults when absent or
malformed), no import artifacts, plugins or dynlibs. Imports then resolve through `LEAN_PATH`,
to the `.olean`s trust-run imported, and no project native code runs. -/
def rebuildSetup (m : Name) (olean : FilePath) : IO ModuleSetup := do
  let rel := "/".intercalate (m.components.map (·.toString))
  let tail := s!"/lib/lean/{rel}.olean"
  let o := olean.toString
  let lake : FilePath := (o.dropEnd tail.length).toString / "ir" / s!"{rel}.setup.json"
  let s : ModuleSetup ←
    if o.endsWith tail && (← lake.pathExists) then
      try ModuleSetup.load lake catch _ => pure { name := m }
    else pure { name := m }
  return { name := m, package? := s.package?, isModule := s.isModule, options := s.options }

/-- `[olean]` facts (D65): each `(module, imported .olean, source)` whose compiled files differ
from FVA's build of its source, whose build fails, or which has no source. The builds run
`sysroot`'s `lean` under `sandbox` (the project's `bwrap` arguments with `tmp` writable; empty =
none), three side by side (each maps its whole import closure), each within `limit` seconds. -/
def rebuildMismatches (mods : Array (Name × FilePath × Option FilePath)) (sysroot : FilePath)
    (sandbox : Array String) (tmp : FilePath) (limit : Nat) : IO (Array String) := do
  let one (i : Nat) (m : Name) (olean : FilePath) (src? : Option FilePath) :
      IO (Option String) := do
    let some src := src? | return some s!"{m}: no source to build it from ({olean})"
    let out := tmp / s!"rebuild-{i}.olean"
    let setup := tmp / s!"rebuild-{i}.json"
    IO.FS.writeFile setup (toJson (← rebuildSetup m olean)).compress
    let cmd := #["timeout", "-k", "10", toString limit, (sysroot / "bin" / "lean").toString,
      src.toString, "-o", out.toString, "-i", (tmp / s!"rebuild-{i}.ilean").toString,
      "--setup", setup.toString, "--json"]
    let (c, args) := if sandbox.isEmpty then (cmd[0]!, cmd.extract 1)
      else ("bwrap", sandbox ++ #["--"] ++ cmd)
    let p ← IO.Process.output { cmd := c, args, stdin := .null }
    if p.exitCode != 0 then return some s!"{m}: FVA's build of {src} failed (rc {p.exitCode})"
    let ds ← oleanDigests #[olean, out]
    if (ds.get? out.toString).isSome && ds.get? olean.toString == ds.get? out.toString then
      return none
    return some s!"{m}: compiled files differ from FVA's build of {src} ({olean})"
  let mut out := #[]
  for b in List.range ((mods.size + 2) / 3) do
    let tasks ← (List.range' (3 * b) 3).filterMapM fun i => do
      let some (m, o, s) := mods[i]? | return none
      return some (← IO.asTask (one i m o s) (prio := .dedicated))
    for t in tasks do
      match ← IO.wait t with
      | .ok (some e) => out := out.push e
      | .ok none => pure ()
      | .error e => out := out.push s!"FVA's build of a spec-closure module failed: {e}"
  return out

end FVA.Trust
