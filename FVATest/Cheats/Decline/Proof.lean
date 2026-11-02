import FVATest.Cheats.Decline.Spec
import Lean.Elab.Command

/-! Cheat Decline (D61): a false theorem whose type names a true theorem called like lean4lean's
heartbeat-limit message, so lean4lean's refutation prints that name on a later line of its
message; the refutation must stay a reject. -/

namespace Cheats.Decline

/-- True; named like the message lean4lean prints when it runs out of heartbeats. -/
theorem «deterministic timeout» : True := trivial

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `Cheats.Decline.one_eq_two, levelParams := [],
  type := mkApp (.lam `h (mkConst ``True) (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1)
    (mkNatLit 2)) .default) (mkConst `Cheats.Decline.«deterministic timeout»),
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) }

theorem holds_proof : holds := one_eq_two

end Cheats.Decline
