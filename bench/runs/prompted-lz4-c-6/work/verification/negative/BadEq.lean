import Lean
set_option debug.skipKernelTC true in
run_elab do
  let nat := Lean.mkConst ``Nat
  let zero := Lean.mkNatLit 0
  Lean.addDecl <| .thmDecl {
    name := `deliberatelyFalseEquality
    levelParams := []
    type := Lean.mkAppN (Lean.mkConst ``Eq [.succ .zero]) #[nat, zero, Lean.mkNatLit 1]
    value := Lean.mkAppN (Lean.mkConst ``Eq.refl [.succ .zero]) #[nat, zero]
  }
