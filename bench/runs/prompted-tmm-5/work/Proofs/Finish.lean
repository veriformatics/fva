import Proofs.Compute
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

theorem cutoff_safe (p : Nat × Nat) (hp : p ∈ pairs) :
    (-10^10 : ℝ) < Real.log (abundanceRatio p) / (2 * Real.log 2) := by
  obtain ⟨hq, hi⟩ := abundance_certificate p hp
  have hq' : (0 : ℝ) < abundanceRatio p := by exact_mod_cast hq
  have hi' : 1 / (abundanceRatio p : ℝ) < 1000000 := by exact_mod_cast hi
  have hl := Real.one_sub_inv_le_log_of_pos hq'
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h2
  rw [inv_eq_one_div] at hl
  apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * Real.log 2)).2
  linarith

theorem raw_ratio_lower (a : Nat) (ha : a ∈ [1,6]) :
    (1181/1000 : ℝ) < Real.exp (logMean (retained a 20)) := by
  obtain ⟨hp, hw, hb⟩ := rational_certificate a ha
  have hs :
      ((((retained a 20).map (fun p => weight p * logLower (ratio p))).sum : ℚ) : ℝ) ≤
      ((retained a 20).map (fun p => (weight p : ℝ) * Real.log (ratio p))).sum := by
    push_cast
    simp only [List.map_map, Function.comp_def, Rat.cast_mul]
    apply List.sum_le_sum
    intro p hpm
    exact mul_le_mul_of_nonneg_left (logLower_sound _ (hp p hpm).2)
      (by exact_mod_cast (hp p hpm).1.le)
  have hw' : (0 : ℝ) < (((retained a 20).map weight).sum : ℚ) := by exact_mod_cast hw
  have hb' :
      (181/1000 : ℝ) * (((retained a 20).map weight).sum : ℚ) <
      ((((retained a 20).map (fun p => weight p * logLower (ratio p))).sum : ℚ) : ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hb
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh
  have hm : (181/1000 : ℝ) < logMean (retained a 20) := by
    apply (lt_div_iff₀ hw').2
    exact hb'.trans_le hs
  have he := Real.add_one_le_exp (logMean (retained a 20))
  linarith

theorem cannot_fit (v : List ℚ) (ps : List (Nat × Nat))
    (hr : (1181/1000 : ℝ) < Real.exp (logMean ps))
    (hgap : v.getD 2 0 + 1/10^10 <
      (v.getD 3 0 - 1/10^10) * (1181/1000 : ℚ)) : ¬ Compatible v ps := by
  rintro ⟨c,hc,hc4,hc3⟩
  obtain ⟨hc4l,hc4u⟩ := abs_le.mp hc4
  obtain ⟨hc3l,hc3u⟩ := abs_le.mp hc3
  have hgap' : (v.getD 2 0 : ℝ) + 1/10^10 <
      ((v.getD 3 0 : ℝ) - 1/10^10) * (1181/1000 : ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hgap
    push_cast at hh
    exact hh
  have hmul : c * (1181/1000 : ℝ) < c * Real.exp (logMean ps) :=
    mul_lt_mul_of_pos_left hr hc
  nlinarith

theorem artifact_gaps :
    ∀ v ∈ [Artifact.edge, Artifact.rna],
      (1/2 : ℚ) < v.getD 3 0 ∧
      v.getD 2 0 + 1/10^10 <
        (v.getD 3 0 - 1/10^10) * (1181/1000 : ℚ) := by decide +kernel

theorem R1_fails : ¬ Compatible Artifact.edge (retained 1 20) :=
  cannot_fit _ _ (raw_ratio_lower 1 (by simp))
    (artifact_gaps _ (by simp)).2

theorem R2_fails : ¬ Compatible Artifact.rna (retained 1 20) :=
  cannot_fit _ _ (raw_ratio_lower 1 (by simp))
    (artifact_gaps _ (by simp)).2

-- Also covers the docstring's literal use of m_trim for A, i.e. 30% A trimming.
theorem R2_literal_bullet_fails : ¬ Compatible Artifact.rna (retained 6 20) :=
  cannot_fit _ _ (raw_ratio_lower 6 (by simp))
    (artifact_gaps _ (by simp)).2

theorem R3_counterexample :
    (9/1000 : ℚ) < |Artifact.edge.getD 0 0 - Artifact.rna.getD 0 0| := by decide +kernel

theorem R3_fails : ¬ Agree10 := by
  intro h
  have hh := h 0 (by simp)
  exact (not_lt_of_ge hh) (lt_trans (by norm_num) R3_counterexample)
end Verification
