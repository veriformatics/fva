import Proofs.Bounds
import Proofs.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

-- Both order statistics bracketing (454-1)*.75 = 339.75 equal this value.
theorem quartile_brackets : ∀ j ∈ List.range 7,
    ((col j).filter (fun v => v < quartiles.getD j 0)).length ≤ 339 ∧
    341 ≤ ((col j).filter (fun v => v ≤ quartiles.getD j 0)).length := by decide +kernel

theorem matrix_shape : Artifact.counts.length = 454 ∧
    ∀ r ∈ Artifact.counts, r.length = 7 ∧ r.sum > 0 := by decide +kernel

theorem library_sizes : (List.range 7).map lib = [1261,621,755,1097,1916,1136,1219] := by decide +kernel

theorem reference_is_four :
    (List.range 7).map uq = [4/1261,2/621,2/755,3/1097,5/1916,3/1136,3/1219] ∧
    (∀ j ∈ List.range 7, (1/10^20 : ℚ) < uq j) ∧
    (∀ j ∈ List.range 7, j ≠ 3 → |uq 3 - uqMean| < |uq j - uqMean|) := by decide +kernel

theorem eligible_count : pairs.length = 205 := by decide +kernel

theorem abundance_certificate : ∀ p ∈ pairs,
    0 < abundanceRatio p ∧ 1 / abundanceRatio p < (1000000 : ℚ) := by
  have hl2 : lib 2 = 755 := by decide +kernel
  have hl3 : lib 3 = 1097 := by decide +kernel
  simp only [abundanceRatio, hl2, hl3]
  decide +kernel

theorem retained_default_eq : retained 1 20 = Certificate.default := by decide +kernel

theorem retained_literal_eq : retained 6 20 = Certificate.literal := by decide +kernel

theorem retained_count : (retained 1 20).length = 76 := by
  rw [retained_default_eq]
  decide

theorem rational_certificate :
    ∀ a ∈ [1, 6],
      (∀ p ∈ retained a 20, 0 < weight p ∧ 0 < ratio p) ∧
      0 < ((retained a 20).map weight).sum ∧
      (181/1000 : ℚ) * ((retained a 20).map weight).sum <
        ((retained a 20).map (fun p => weight p * logLower (ratio p))).sum := by
  have hl2 : lib 2 = 755 := by decide +kernel
  have hl3 : lib 3 = 1097 := by decide +kernel
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · rw [retained_default_eq]
    simp only [weight, ratio, hl2, hl3]
    decide +kernel
  · rw [retained_literal_eq]
    simp only [weight, ratio, hl2, hl3]
    decide +kernel
end Verification
