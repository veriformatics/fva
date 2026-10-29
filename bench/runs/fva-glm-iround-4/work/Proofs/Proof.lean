import Proofs.Spec
import FVA.Proof.Lib
import Mathlib.Tactic.NormNum

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem R1Counterexample_holds : R1Counterexample := by
  have hv : ofBits f64fmt (0x3fdfffffffffffff : BitVec 64) =
      .normal false 4503599627370495 (-2) := by decide +kernel
  have hr : (ofBits f64fmt (0x3fdfffffffffffff : BitVec 64)).toReal f64fmt =
      (9007199254740991 : ℝ) / 18014398509481984 := by
    rw [hv]
    norm_num [FVal.toReal, f64fmt, zpow_neg]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨by rw [hv]; trivial, hr, ?_, ?_, ?_, ?_⟩
  · rw [hr]; norm_num
  · rw [hr]; norm_num
  · rw [hr]; norm_num
  · refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
    intro H s inst h
    have ha := instance_alloc rfl rfl rfl rfl h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    refine ⟨0, rfl, ⟨_, rfl, by exact .cons trivial .nil⟩, ?_⟩
    apply must_returned_of_runDet (n := 20)
        (s' := (allocModule {} Lifted.module [] [] []).1) (f' := ⟨[], {}⟩)
        (vs := [.i32 1])
    · kernel_rfl
    · rfl

end Proofs
