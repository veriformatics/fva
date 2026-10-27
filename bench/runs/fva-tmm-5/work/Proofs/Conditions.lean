import Proofs.Proof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TMM

theorem log2_lower (a n : Nat) (ha : 0 < a) (hn : 0 < n) (hmax : n ≤ 2000) :
    (-4000 : ℝ) < Real.log ((a : ℝ) / n) / Real.log 2 := by
  have han : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm : (n : ℝ) ≤ 2000 := by exact_mod_cast hmax
  have hx : (1/2000 : ℝ) ≤ (a : ℝ)/n := by
    apply (le_div_iff₀ hnr).mpr
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<1/2000) hx
  have hmin := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<1/2000)
  norm_num at hmin
  have htwo := Real.le_log_one_add_of_nonneg (show (0:ℝ) ≤ 1 by norm_num)
  norm_num at htwo
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  linarith

end TMM

namespace Proofs
open TMM

theorem cutoff_inactive : ∀ p ∈ pairs matrix 2 3,
    (-10^10 : ℝ) <
      (Real.log ((p.1 : ℝ)/library matrix 2) / Real.log 2 +
       Real.log ((p.2 : ℝ)/library matrix 3) / Real.log 2) / 2 := by
  intro p hp
  have hpos : 0 < p.1 ∧ 0 < p.2 := by
    simpa using (List.mem_filter.mp hp).2
  have h1 := log2_lower p.1 _ hpos.1 (library_bounds 2 (by decide)).1
    (library_bounds 2 (by decide)).2
  have h2 := log2_lower p.2 _ hpos.2 (library_bounds 3 (by decide)).1
    (library_bounds 3 (by decide)).2
  linarith

theorem positive_pair_count : (pairs matrix 2 3).length = 205 := by decide +kernel
theorem retained_count : (retained matrix 2 3).length = 76 := by
  rw [retained_eq]; decide

theorem tied_half_rank : rank2
    ((pairs matrix 2 3).map (fun p => (p.1 : ℚ)/p.2)) (1/2) = 114 := by decide +kernel

theorem gene451_counts : (matrix[450]!)[2]! = 5 ∧ (matrix[450]!)[3]! = 10 := by decide +kernel

theorem reference_raw_eq_one : Real.exp (meanLog matrix 3 3) = 1 := by
  have hpairs : ∀ p ∈ pairs matrix 3 3, expressionRatio 1097 1097 p = 1 := by decide +kernel
  have h : ∀ p ∈ retained matrix 3 3, expressionRatio 1097 1097 p = 1 := by
    intro p hp
    exact hpairs p (List.mem_filter.mp hp).1
  unfold meanLog
  rw [nR_eq]
  dsimp only
  have hn : ((retained matrix 3 3).map fun p =>
      (weight 1097 1097 p : ℝ) * Real.log (expressionRatio 1097 1097 p)).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    rw [h p hp, Rat.cast_one, Real.log_one, mul_zero]
  rw [hn, zero_div, Real.exp_zero]

end Proofs
