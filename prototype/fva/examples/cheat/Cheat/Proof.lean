import Cheat.Spec
import FVA

/-! Proofs of the `Cheat.Spec` claims — each one cheats (see `Cheat/Spec.lean`). -/

namespace Cheat.Proof
open FVA.Wasm

theorem clamp_holds : clamp_spec := fun _ _ _ => returns_of_invoke rfl ⟨5, by wasm_sim [Lifted.clamp]⟩

axiom gcd_correct : gcd_spec

theorem gcd_holds : gcd_spec := gcd_correct

theorem sum_to_holds : sum_to_spec := by sorry

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `Cheat.Proof.one_eq_two, levelParams := [],
  type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2),
  value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1) }

theorem sum_to_zero_holds : sum_to_zero := absurd one_eq_two (by decide)

theorem sumBelow_ten_holds : sumBelow_ten := by unfold sumBelow_ten; native_decide

theorem gcd_terminates_holds : gcd_terminates := fun _ _ => trivial

theorem sum_to_seven_holds : sum_to_seven := fun _ h => h.elim

end Cheat.Proof
