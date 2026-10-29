import Lean
open Lean Elab Command

-- A second poisoned theorem, claiming (1 : Nat) = 2 by reflexivity of 1.
set_option debug.skipKernelTC true
elab "inject_unequal_proof" : command => liftCoreM do
  let ty := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) (mkNatLit 1)
  addDecl (.thmDecl { name := `knownUnequal, levelParams := [], type := ty, value := value })
inject_unequal_proof
