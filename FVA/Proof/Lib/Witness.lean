import FVA.Trust.Obligation

/-!
# `fva_obligation% C` (U37, contract `docs/contracts/U37-witness.md`)

The statement a `@[fva_witness C]` theorem proves: claim `C`'s domain obligation, computed by
`FVA.Trust.obligation` — the function `fva trust` runs — so the theorem's type is the obligation the
collector derives (`fva trust` compares the two expressions). Origins here are read from module
names: Lean core, Mathlib's packages and FVA (outside the package of `C`) stop unfolding; `fva
trust` classifies by file, so a module those two rules place apart shows as a rejected witness.
-/

namespace FVA.Proof
open Lean Elab Term

/-- Module-name roots whose definitions stay folded on the proof side. -/
def foldedRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
   `ImportGraph, `LeanSearchClient, `Cli, `FVA]

/-- `c` belongs to the project or a subject (proof side): declared here, in the package of the
judged claim (`pre`), or in a module outside `foldedRoots`. -/
def projectSide (env : Environment) (pre : Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    pre.isPrefixOf m || !foldedRoots.contains m.getRoot

/-- `fva_obligation% C`: claim `C`'s domain obligation (contract U37 C1). -/
elab "fva_obligation% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let env ← getEnv
  let pre := ((env.getModuleIdxFor? n).map fun (i : ModuleIdx) =>
    env.header.moduleNames[i.toNat]!).getD .anonymous |>.getPrefix
  match ← FVA.Trust.obligation (projectSide env pre) n with
  | .required e => return e
  | .notRequired => throwError "{n} has no input domain to witness"
  | .unavailable why => throwError "{n}: no obligation ({why})"

end FVA.Proof
