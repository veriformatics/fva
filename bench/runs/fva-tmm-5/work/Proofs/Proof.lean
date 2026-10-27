import Proofs.Data
import Proofs.LogBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs
open TMM

theorem reference_unique : UniqueReference matrix 3 := by
  unfold UniqueReference
  rw [quartiles_eq]
  refine ⟨by decide, ?_, ?_⟩
  · norm_num
  · intro j hj hne
    interval_cases j <;> norm_num at *

theorem library_bounds : ∀ j < 7, 0 < library matrix j ∧ library matrix j ≤ 2000 := by
  intro j hj
  have hh : library matrix j = ([1261, 621, 755, 1097, 1916, 1136, 1219] : List Nat)[j]! := by
    have := congrArg (fun xs => xs[j]!) libraries
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this
  rw [hh]
  interval_cases j <;> decide

theorem kept_positive : ∀ p ∈ kept,
    0 < expressionRatio 755 1097 p ∧ 0 ≤ weight 755 1097 p := by decide +kernel

def lowerNumerator : ℚ :=
  (kept.map fun p => weight 755 1097 p * logLower (expressionRatio 755 1097 p)).sum

def denominator : ℚ := (kept.map (weight 755 1097)).sum

theorem denominator_pos : 0 < denominator := by decide +kernel

theorem lowerNumerator_gt : (177/1000 : ℚ) * denominator < lowerNumerator := by decide +kernel

theorem sum_log_lower (ps : List (Nat × Nat))
    (h : ∀ p ∈ ps, 0 < expressionRatio 755 1097 p ∧ 0 ≤ weight 755 1097 p) :
    (((ps.map fun p => weight 755 1097 p * logLower (expressionRatio 755 1097 p)).sum : ℚ) : ℝ) ≤
      (ps.map fun p => (weight 755 1097 p : ℝ) * Real.log (expressionRatio 755 1097 p)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (log_lower _ (h p (by simp)).1)
        (by exact_mod_cast (h p (by simp)).2)
    · exact ih (fun p hp => h p (by simp [hp]))

theorem mean_gt : (177/1000 : ℝ) < meanLog matrix 2 3 := by
  unfold meanLog
  rw [retained_eq, nO_eq, nR_eq]
  change (177/1000 : ℝ) < _ / (denominator : ℝ)
  apply (lt_div_iff₀ (by exact_mod_cast denominator_pos : (0 : ℝ) < denominator)).mpr
  have h : (177/1000 : ℝ) * (denominator : ℝ) < (lowerNumerator : ℝ) := by
    have hh : (((177/1000 : ℚ) * denominator : ℚ) : ℝ) < (lowerNumerator : ℝ) :=
      (Rat.cast_lt (K := ℝ)).2 lowerNumerator_gt
    norm_num at hh ⊢
    exact hh
  exact h.trans_le (sum_log_lower kept kept_positive)

theorem rawFactor_gt : (119/100 : ℝ) < Real.exp (meanLog matrix 2 3) := by
  have hp : (119/100 : ℝ) < (2011/2000 : ℝ)^32 := by norm_num
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 119/100) hp
  rw [Real.log_pow] at hlog
  have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2011/2000)
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 119/100)).mp
  have hsmall : Real.log (119/100 : ℝ) < 177/1000 := by linarith
  exact hsmall.trans mean_gt

theorem reject_pair (ds : List Dec)
    (hgap : (ds[2]!.value : ℝ) + 1/10^10 <
      (119/100 : ℝ) * ((ds[3]!.value : ℝ) - 1/10^10)) :
    ∀ g : ℝ, 0 < g →
      ¬ (|Real.exp (meanLog matrix 2 3) / g - (ds[2]!.value : ℝ)| ≤ 1/10^10 ∧
         |1/g - (ds[3]!.value : ℝ)| ≤ 1/10^10) := by
  intro g hg h
  have h3 := (abs_le.mp h.1).2
  have h4 := (abs_le.mp h.2).1
  have hr := div_lt_div_of_pos_right rawFactor_gt hg
  have hr' : (119/100 : ℝ) * (1/g) < Real.exp (meanLog matrix 2 3) / g := by
    simpa [div_eq_mul_inv] using hr
  linarith only [h3, h4, hr', hgap]

theorem edger_gap : (edger[2]!.value : ℝ) + 1/10^10 <
    (119/100 : ℝ) * ((edger[3]!.value : ℝ) - 1/10^10) := by
  norm_num [edger, Dec.value]

theorem rnanorm_gap : (rnanorm[2]!.value : ℝ) + 1/10^10 <
    (119/100 : ℝ) * ((rnanorm[3]!.value : ℝ) - 1/10^10) := by
  norm_num [rnanorm, Dec.value]

theorem edger_valid : ∀ d ∈ edger, d.Valid := by
  norm_num [edger, Dec.Valid]

theorem rnanorm_valid : ∀ d ∈ rnanorm, d.Valid := by
  norm_num [rnanorm, Dec.Valid]

theorem R1_failure_holds : R1_failure := by
  refine ⟨matrix, edger, counts_bytes, edger_bytes, matrix_length, matrix_shape,
    by decide, edger_valid, library_bounds, reference_unique, reject_pair edger edger_gap⟩

theorem R2_failure_holds : R2_failure := by
  refine ⟨matrix, rnanorm, counts_bytes, rnanorm_bytes, matrix_length, matrix_shape,
    by decide, rnanorm_valid, library_bounds, reference_unique, reject_pair rnanorm rnanorm_gap⟩

theorem R3_failure_holds : R3_failure := by
  refine ⟨edger, rnanorm, edger_bytes, rnanorm_bytes, by decide, by decide, edger_valid, rnanorm_valid, ?_⟩
  norm_num [edger, rnanorm, Dec.value]

end Proofs
