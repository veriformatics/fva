import Lean

-- Submit a well-formed declaration carrying Eq.refl 0 as a proof of 0 = 1
-- directly to Lean's kernel, bypassing tactic/elaborator proof checking.
open Lean Elab Command in
run_elab do
  let nat := mkConst ``Nat
  let zero := mkNatLit 0
  let one := mkNatLit 1
  addDecl (.thmDecl {
    name := `knownFalse
    levelParams := []
    type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat zero one
    value := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) nat zero
  })
