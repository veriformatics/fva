import Lean
open Lean Elab Command

run_elab do
  let zero := mkNatLit 0
  let eq := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) zero (mkNatLit 1)
  let refl := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) zero
  let decl := Declaration.thmDecl {
    name := `Forged.wrongEquality
    levelParams := []
    type := eq
    value := refl
  }
  match (← getEnv).addDeclCore 0 0 decl none false with
  | .ok env => setEnv env
  | .error _ => throwError "could not construct negative control"
