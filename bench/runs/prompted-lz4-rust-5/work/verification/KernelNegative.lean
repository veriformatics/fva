import Lean
open Lean Elab Command
-- These declarations bypass proof elaboration and are submitted to the kernel.
run_elab do
  liftM (m := CoreM) do
    let nat := mkConst ``Nat
    let zero := mkNatLit 0
    let badType := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) nat zero (mkNatLit 1)
    let value := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) nat zero
    addDecl (.thmDecl { name := `ForgedUnequal, levelParams := [], type := badType, value := value })
run_elab do
  liftM (m := CoreM) do
    let value := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Nat) (mkNatLit 0)
    addDecl (.thmDecl { name := `ForgedFalse, levelParams := [], type := mkConst ``False, value := value })
