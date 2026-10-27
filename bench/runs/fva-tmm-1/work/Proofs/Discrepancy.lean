import Proofs.WitnessData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs

theorem R3Fails_holds : R3Fails := by
  refine ⟨Witness.edger, Witness.rnanorm, Witness.edger_eq, Witness.rnanorm_eq, rfl, rfl, ?_⟩
  have gap : ∀ j ∈ List.range 7, (1 / 1000 : ℚ) <
      |decimalValue Witness.edger[j]! - decimalValue Witness.rnanorm[j]!| := by decide +kernel
  intro j hj
  have h := (Rat.cast_lt (K := ℝ)).mpr (gap j hj)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_abs, Rat.cast_sub] using h

end Proofs
