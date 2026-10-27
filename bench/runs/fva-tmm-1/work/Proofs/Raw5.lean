import Proofs.LogBounds
import Proofs.Coefficients5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric

theorem raw5 : ((-126931 / 5000000) : ℝ) ≤ rawLog Witness.matrix 5 3 ∧
    rawLog Witness.matrix 5 3 ≤ ((-253861 / 10000000) : ℝ) := by
  have h := evalLogs_bounds lb ub log_bounds cs5
  change _ ≤ evalLogs (rawCoeffs Witness.matrix 5 3) ∧ evalLogs (rawCoeffs Witness.matrix 5 3) ≤ _
  rw [coeffs5]
  have hl : ((-126931 / 5000000) : ℚ) ≤ (cs5.map (lowerTerm lb ub)).sum := by decide +kernel
  have hu : (cs5.map (upperTerm lb ub)).sum ≤ ((-253861 / 10000000) : ℚ) := by decide +kernel
  have hl' := (Rat.cast_le (K := ℝ)).mpr hl
  have hu' := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_neg] at hl' hu'
  exact ⟨le_trans hl' h.1, le_trans h.2 hu'⟩
end Proofs.Numeric
