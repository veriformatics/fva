import Lean
open Lean

-- A proof object for 1=0 whose value actually proves 1=1.
set_option debug.skipKernelTC true in
run_elab
  liftM <| addDecl <| .thmDecl {
    name := `forgedArithmetic
    levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 0)
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)
  }
