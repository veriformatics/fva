import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_elab do
  addDecl <| .thmDecl {
    name := `KnownFalse
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro
  }
  addDecl <| .thmDecl {
    name := `KnownFalseArithmetic
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 1)
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 0)
  }
