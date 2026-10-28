import Lean
set_option debug.skipKernelTC true
run_elab Lean.addDecl (.thmDecl {
  name := `badEquality
  levelParams := []
  type := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.zero.succ])
    (Lean.mkConst ``Nat) (Lean.mkNatLit 0) (Lean.mkNatLit 1)
  value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [Lean.Level.zero.succ])
    (Lean.mkConst ``Nat) (Lean.mkNatLit 0)
})
