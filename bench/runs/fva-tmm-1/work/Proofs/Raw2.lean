import Proofs.LogBounds
import Proofs.Coefficients2
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric

theorem raw2 : ((14248 / 78125) : ℝ) ≤ rawLog Witness.matrix 2 3 ∧
    rawLog Witness.matrix 2 3 ≤ ((364749 / 2000000) : ℝ) := by
  have h := evalLogs_bounds lb ub log_bounds cs2
  change _ ≤ evalLogs (rawCoeffs Witness.matrix 2 3) ∧ evalLogs (rawCoeffs Witness.matrix 2 3) ≤ _
  rw [coeffs2]
  have hl : ((14248 / 78125) : ℚ) ≤ (cs2.map (lowerTerm lb ub)).sum := by decide +kernel
  have hu : (cs2.map (upperTerm lb ub)).sum ≤ ((364749 / 2000000) : ℚ) := by decide +kernel
  have hl' := (Rat.cast_le (K := ℝ)).mpr hl
  have hu' := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_neg] at hl' hu'
  exact ⟨le_trans hl' h.1, le_trans h.2 hu'⟩
end Proofs.Numeric
