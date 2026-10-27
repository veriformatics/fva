import Proofs.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TMM

theorem r3_all_samples_fail_rational : ∀ i ∈ List.range 7,
    (1:ℚ)/10^10 < |edgeFactors[i]! - rnaFactors[i]!| := by
  decide +kernel

theorem r3_all_samples_fail : ∀ i ∈ List.range 7,
    ((1:ℚ)/10^10 :ℝ) < |(edgeFactors[i]! : ℝ) - (rnaFactors[i]! : ℝ)| := by
  intro i hi
  exact_mod_cast r3_all_samples_fail_rational i hi

theorem r3_rounded_decimals_fail : ∀ i ∈ List.range 7,
    ⌊edgeFactors[i]! * 10^10 + 1/2⌋ ≠ ⌊rnaFactors[i]! * 10^10 + 1/2⌋ := by
  decide +kernel

theorem sample_one_difference : edgeFactors[0]! - rnaFactors[0]! =
    (931142302732627:ℚ)/10^17 := by
  decide +kernel
end TMM
