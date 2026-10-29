-- INTENTIONALLY INVALID. Used only to test the checking tools.
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true in
run_elab do
  liftM <| addDecl <| .thmDecl {
    name := `badFalse, levelParams := [], type := mkConst ``False,
    value := mkConst ``True.intro }
set_option debug.skipKernelTC true in
run_elab do
  liftM <| addDecl <| .thmDecl {
    name := `badEquality, levelParams := [],
    type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 1),
    value := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit 0) }
