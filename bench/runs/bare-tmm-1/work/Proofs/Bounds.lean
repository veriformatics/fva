import Proofs.Model

namespace Verification

lemma logLower_sound (q : ℚ) (hq : 0 < q) : (logLower q : ℝ) ≤ Real.log (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let z : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hd : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hz : |z| < 1 := by
    rw [abs_lt]
    constructor
    · dsimp [z]; rw [lt_div_iff₀ hd]; linarith
    · dsimp [z]; rw [div_lt_iff₀ hd]; linarith
  have heq : (1 + z) / (1 - z) = (q : ℝ) := by
    dsimp [z]
    field_simp
    ring
  have h := Real.sum_range_sub_log_div_le hz 3
  rw [heq] at h
  have hs : (∑ i ∈ Finset.range 3, z ^ (2 * i + 1) / (2 * i + 1)) =
      z + z^3 / 3 + z^5 / 5 := by norm_num [Finset.sum_range_succ]
  rw [hs] at h
  have hh := (abs_le.mp h).1
  have hc : (logLower q : ℝ) =
      2 * (z + z^3 / 3 + z^5 / 5) - 2 * |z|^7 / (1 - z^2) := by
    dsimp [logLower, z]
    push_cast
    rfl
  rw [hc]
  norm_num at hh
  simp only [mul_div_assoc]
  linarith only [hh]

lemma weighted_lower (j : Nat) (ps : List Pair)
    (hp : ∀ p ∈ ps, 0 < ratio j p ∧ 0 ≤ weight j p)
    (hw : 0 < (ps.map (weight j)).sum) :
    (((ps.map (fun p => weight j p * logLower (ratio j p))).sum /
      (ps.map (weight j)).sum : ℚ) : ℝ) ≤ weightedLog j ps := by
  have hs : (ps.map (fun p => ((weight j p : ℝ) * (logLower (ratio j p) : ℝ)))).sum ≤
      (ps.map (fun p => (weight j p : ℝ) * Real.log (ratio j p))).sum := by
    clear hw
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp0 := hp p (by simp)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (logLower_sound _ hp0.1)
          (by exact_mod_cast hp0.2)
      · exact ih (fun p h => hp p (by simp [h]))
  have hsCast : ((ps.map (fun p => weight j p * logLower (ratio j p))).sum : ℝ) =
      (ps.map (fun p => (weight j p : ℝ) * (logLower (ratio j p) : ℝ))).sum := by
    simp [Function.comp_def]
  have hwCast : ((ps.map (weight j)).sum : ℝ) =
      (ps.map (fun p => (weight j p : ℝ))).sum := by simp [Function.comp_def]
  have hwR : (0 : ℝ) < ((ps.map (weight j)).sum : ℝ) := by exact_mod_cast hw
  rw [Rat.cast_div, hsCast, hwCast, weightedLog]
  exact div_le_div_of_nonneg_right hs (by rw [← hwCast]; exact hwR.le)

end Verification
