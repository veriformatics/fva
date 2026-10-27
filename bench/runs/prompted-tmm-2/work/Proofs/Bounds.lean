import Proofs.Spec

namespace TMM
def z (r : ℚ) : ℚ := (r-1)/(r+1)
def approx (r : ℚ) : ℚ := 2 * (z r + z r ^ 3 / 3)
def error (r : ℚ) : ℚ := 2 * |z r| ^ 5 / (1-z r ^ 2)
def lower (r : ℚ) : ℚ := 4 * (approx r - error r)
def upper (r : ℚ) : ℚ := 4 * (approx r + error r)

theorem log_bounds (r : ℚ) (hr : 0 < r) :
    ((approx r - error r : ℚ) : ℝ) ≤ Real.log (r : ℝ) ∧
    Real.log (r : ℝ) ≤ ((approx r + error r : ℚ) : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : (r : ℝ) + 1 ≠ 0 := by linarith
  let t : ℝ := ((r : ℝ) - 1) / ((r : ℝ) + 1)
  have ht : |t| < 1 := by
    rw [abs_lt]
    constructor <;> dsimp [t]
    · apply (lt_div_iff₀ (by linarith : (0 : ℝ) < r+1)).2
      linarith
    · apply (div_lt_iff₀ (by linarith : (0 : ℝ) < r+1)).2
      linarith
  have heq : (1+t)/(1-t) = (r : ℝ) := by dsimp [t]; field_simp; ring
  have h := Real.sum_range_sub_log_div_le ht 2
  rw [heq] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  norm_num at h
  have hz : ((z r : ℚ) : ℝ) = t := by simp [z, t]
  have ha : ((approx r : ℚ) : ℝ) = 2*(t+t^3/3) := by simp [approx, hz]
  have he : ((error r : ℚ) : ℝ) = 2*|t|^5/(1-t^2) := by simp [error, hz]
  push_cast
  rw [ha, he]
  simp only [mul_div_assoc]
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

theorem root_bounds (q l u : ℚ) (hl : 0 < l) (hu : 0 < u)
    (hql : l^4 ≤ q) (hqu : q ≤ u^4) :
    ((lower l : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧
    Real.log (q : ℝ) ≤ ((upper u : ℚ) : ℝ) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hql' : (l : ℝ)^4 ≤ q := by exact_mod_cast hql
  have hqu' : (q : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast hqu
  have hq : (0 : ℝ) < q := lt_of_lt_of_le (pow_pos hl' 4) hql'
  have A := Real.log_le_log (pow_pos hl' 4) hql'
  have B := Real.log_le_log hq hqu'
  rw [Real.log_pow] at A B
  have C := log_bounds l hl
  have D := log_bounds u hu
  push_cast at C D
  norm_num at A B
  simp only [lower, upper, Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_ofNat]
  constructor <;> linarith [C.1, D.2]

end TMM

namespace TMM
-- A certificate carries a rational interval for each logarithm.
structure Term where
  q : ℚ
  w : ℚ
  lo : ℚ
  hi : ℚ

def Term.valid (t : Term) : Prop :=
  0 ≤ t.w ∧ (t.lo : ℝ) ≤ Real.log (t.q : ℝ) ∧ Real.log (t.q : ℝ) ≤ (t.hi : ℝ)
def weights (ts : List Term) : ℚ := (ts.map (·.w)).sum
def lowMean (ts : List Term) : ℚ := (ts.map fun t => t.w*t.lo).sum / weights ts
def highMean (ts : List Term) : ℚ := (ts.map fun t => t.w*t.hi).sum / weights ts

theorem sum_bounds (ts : List Term) (hs : ∀ t ∈ ts, t.valid) :
    (((ts.map fun t => t.w*t.lo).sum : ℚ) : ℝ) ≤
      (ts.map fun t => (t.w : ℝ)*Real.log (t.q : ℝ)).sum ∧
    (ts.map fun t => (t.w : ℝ)*Real.log (t.q : ℝ)).sum ≤
      (((ts.map fun t => t.w*t.hi).sum : ℚ) : ℝ) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := hs t (by simp)
    have hts := ih (fun u hu => hs u (by simp [hu]))
    have hw : (0 : ℝ) ≤ t.w := by exact_mod_cast ht.1
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left ht.2.1 hw) hts.1,
      add_le_add (mul_le_mul_of_nonneg_left ht.2.2 hw) hts.2⟩

theorem mean_bounds (ts : List Term) (hs : ∀ t ∈ ts, t.valid) (hw : 0 < weights ts) :
    ((lowMean ts : ℚ) : ℝ) ≤ meanLog (ts.map fun t => (t.q,t.w)) ∧
    meanLog (ts.map fun t => (t.q,t.w)) ≤ ((highMean ts : ℚ) : ℝ) := by
  have hw' : (0 : ℝ) < (weights ts : ℚ) := by exact_mod_cast hw
  have heq : ((weights ts : ℚ) : ℝ) = (ts.map fun t => (t.w : ℝ)).sum := by
    simp [weights, Rat.cast_list_sum, List.map_map, Function.comp_def]
  have h := sum_bounds ts hs
  unfold meanLog lowMean highMean
  simp only [List.map_map, Function.comp_def]
  simp only [Rat.cast_div]
  rw [← heq]
  exact ⟨div_le_div_of_nonneg_right h.1 hw'.le, div_le_div_of_nonneg_right h.2 hw'.le⟩
end TMM
