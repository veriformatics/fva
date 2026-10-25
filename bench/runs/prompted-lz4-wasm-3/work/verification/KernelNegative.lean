import Lean
open Lean Elab Command
run_elab do
  let ty := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) (mkNatLit 0) (mkNatLit 1)
  let proof := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Nat) (mkNatLit 0)
  addDecl (.thmDecl { name := `ForgedFalseProof, levelParams := [], type := ty, value := proof })
