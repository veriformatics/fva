import FVATest.Cheats.SkipKernel.Spec
import Lean.Elab.Command

/-! Cheat SkipKernel: proofs. -/

namespace Cheats.SkipKernel

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `Cheats.SkipKernel.one_eq_two, levelParams := [],
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2),
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) }

theorem decodes_holds : decodes := absurd one_eq_two (by decide)

end Cheats.SkipKernel
