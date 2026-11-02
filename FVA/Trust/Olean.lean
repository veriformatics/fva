import Lean

/-!
# `.olean` pins (D48, trusted glue)

A module counts as Mathlib by where its `.olean` lies (contract F2), but the project's build
writes that directory: an edited Mathlib definition, rebuilt in place, would keep its constants
outside the review surface while the claims that use them change meaning, and replay accepts it
(a definition is never refuted). So every such module's compiled bytes must equal the pinned
bytes of FVA's own Mathlib cache at the pinned revision (`trust/oleans.tsv`, written by
`scripts/make-olean-pins`, which computes the same digest in bash, apart from this code).
-/

namespace FVA.Trust

open Lean System

/-- A compiled module's files, in pinned order: Lean's module system splits it into the public
`.olean`, `.olean.server` and `.olean.private`; a module outside that system has the first. -/
def oleanParts (olean : FilePath) : Array FilePath :=
  #[olean, olean.toString ++ ".server", olean.toString ++ ".private"]

/-- sha256 of each existing file (absent ones left out), 256 paths per `sha256sum`, the batches
side by side. -/
def sha256Files (paths : Array FilePath) : IO (Std.HashMap String String) := do
  let present ← paths.filterM (·.pathExists)
  let tasks ← (Array.range ((present.size + 255) / 256)).mapM fun b => IO.asTask do
    let o ← IO.Process.output
      { cmd := "sha256sum", args := (present.extract (256 * b) (256 * b + 256)).map toString }
    if o.exitCode != 0 then throw <| IO.userError s!"sha256sum (rc {o.exitCode}): {o.stderr}"
    return o.stdout
  let mut out := {}
  for t in tasks do
    for l in (← IO.ofExcept (← IO.wait t)).splitOn "\n" do
      if let [h, p] := l.splitOn "  " then out := out.insert p h
  return out

/-- Pin digest of each module (keyed by its `.olean` path): sha256 of `"h₁ h₂ h₃"`, the parts'
sha256 in `oleanParts` order, `-` for an absent part. -/
def oleanDigests (oleans : Array FilePath) : IO (Std.HashMap String String) := do
  let parts ← sha256Files (oleans.flatMap oleanParts)
  let lines := oleans.map fun o =>
    " ".intercalate ((oleanParts o).toList.map fun p => parts.getD p.toString "-")
  IO.FS.withTempDir fun dir => do
    let files := (Array.range lines.size).map fun i => dir / s!"{i}"
    for (f, l) in files.zip lines do IO.FS.writeFile f l
    let hs ← sha256Files files
    return (oleans.zip files).foldl (init := {}) fun m (o, f) =>
      match hs.get? f.toString with
      | some h => m.insert o.toString h
      | none => m

/-- The pins: module name ↦ digest (`trust/oleans.tsv`: `module<TAB>digest`, `#` comments). -/
def readOleanPins (file : FilePath) : IO (Std.HashMap String String) := do
  let mut out := {}
  for l in (← IO.FS.readFile file).splitOn "\n" do
    if let [m, h] := l.splitOn "\t" then
      unless m.startsWith "#" do out := out.insert m h
  return out

/-- `[olean]` facts: each `(module, resolved .olean)` whose digest misses its pin. -/
def oleanMismatches (pins : Std.HashMap String String) (mods : Array (Name × FilePath)) :
    IO (Array String) := do
  let ds ← oleanDigests (mods.map (·.2))
  return mods.filterMap fun (m, f) =>
    match pins.get? (m.toString false) with
    | none => some s!"{m}: not in the pinned .olean set ({f})"
    | some h =>
      if ds.get? f.toString == some h then none
      else some s!"{m}: compiled files differ from the pinned bytes ({f})"

end FVA.Trust
