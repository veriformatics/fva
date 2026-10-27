import Proofs.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Verification
noncomputable def weightedLog2 (ts : List Term) : ℝ :=
  (ts.map fun t => (t.1 : ℝ) * (Real.log (t.2.q : ℝ) / Real.log 2)).sum

lemma weightedLog2_eq (ts : List Term) : weightedLog2 ts = value ts / Real.log 2 := by
  induction ts with
  | nil => simp [weightedLog2,value]
  | cons t ts ih =>
    simp only [weightedLog2,value,List.map_cons,List.sum_cons] at *
    rw [ih]
    ring

/-- Using natural logs in the model is equivalent to exponentiating the weighted
base-2 M-values, as in both implementations. -/
theorem raw_base_two (ts : List Term) : (2 : ℝ) ^ weightedLog2 ts = Real.exp (value ts) := by
  rw [Real.rpow_def_of_pos (by norm_num), weightedLog2_eq]
  have hn : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  congr 1
  field_simp

/-- The model divides every unnormalized factor by the geometric mean. -/
theorem factor_geometric_mean (raw : Fin 7 → ℝ) (i : Fin 7) :
    factor raw i = Real.exp (raw i) / Real.exp ((∑ j, Real.log (Real.exp (raw j))) / 7) := by
  simp [factor, Real.exp_sub]

/-- The exact-real model has the documented product-one normalization. -/
theorem product_factors (raw : Fin 7 → ℝ) : ∏ i, factor raw i = 1 := by
  simp only [factor, ← Real.exp_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  convert Real.exp_zero using 1
  congr 1
  ring
end Verification
