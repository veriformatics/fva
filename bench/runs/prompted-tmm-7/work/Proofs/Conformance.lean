import Proofs.Certificates
import Proofs.Results
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Verify

-- R's type-7 quantile at p=3/4. On this input n=454, so h=339+3/4.
def quartile (i : ℕ) : ℚ :=
  let xs := (matrix.map fun r => r[i]!).insertionSort (· ≤ ·)
  ((xs[339]! : ℚ) + 3 * (xs[340]! : ℚ)) / 4

def quartileDistance (i : ℕ) : ℚ :=
  let qs := (List.range 7).map fun j => quartile j / (lib j : ℚ)
  |qs[i]! - qs.sum / 7|

theorem reference_is_fourth : ∀ i ∈ List.range 7,
    i ≠ 3 → quartileDistance 3 < quartileDistance i := by
  simp only [quartileDistance, quartile, lib, matrix_eq]
  decide +kernel

theorem libraries_bounded : ∀ i < 7, 0 < lib i ∧ lib i ≤ 2000 := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem positive_fraction {o n : ℕ} (ho : 0 < o) (hn : 0 < n) (hn' : n ≤ 2000) :
    (1/2000 : ℝ) ≤ (o : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ 2000 := by exact_mod_cast hn'
  have hoR : (1 : ℝ) ≤ o := by exact_mod_cast ho
  apply (le_div_iff₀ hnR).mpr
  linarith

-- The default A cutoff removes no positive count pairs on this matrix.
theorem cutoff_inactive (q r : ℝ) (hq : 1/2000 ≤ q) (hr : 1/2000 ≤ r) :
    (-10000000000 : ℝ) < (Real.log q + Real.log r) / (2 * Real.log 2) := by
  have hlo : (-1999 : ℝ) ≤ Real.log (1/2000 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1/2000)
    norm_num at h
    exact h
  have hq' := (Real.log_le_log (by norm_num : (0 : ℝ) < 1/2000) hq)
  have hr' := (Real.log_le_log (by norm_num : (0 : ℝ) < 1/2000) hr)
  have h2 := (log_bounds 2 (by norm_num) (by norm_num [z])).1
  norm_num [logLo, poly, err, z] at h2
  apply (lt_div_iff₀ (by linarith : 0 < 2 * Real.log 2)).mpr
  linarith

theorem default_log_bounds :
    (137/1000 : ℝ) ≤ normLog 1 20 2 ∧
    ∀ i < 7,
      (([19,292,182,-1,-160,-26,1] : List ℚ)[i]! / 1000 - 315/7000 : ℚ) ≤ normLog 1 20 i ∧
      normLog 1 20 i ≤ (([20,293,183,1,-159,-25,2] : List ℚ)[i]! / 1000 - 307/7000 : ℚ) := by
  have h0 := bound_default_0
  have h1 := bound_default_1
  have h2 := bound_default_2
  have h3 := bound_default_3
  have h4 := bound_default_4
  have h5 := bound_default_5
  have h6 := bound_default_6
  simp only [normLog, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  constructor
  · linarith [h0.2,h1.2,h2.1,h2.2,h3.2,h4.2,h5.2,h6.2]
  · intro i hi
    interval_cases i <;> norm_num <;> constructor <;> linarith

theorem sample3_gt : (113/100 : ℝ) < tmm 1 20 2 := by
  have h := default_log_bounds.1
  have he := Real.add_one_le_exp (normLog 1 20 2)
  unfold tmm
  linarith

-- Bounds on exp are obtained by comparing its argument to proved log bounds.
theorem exp_interval (x : ℝ) (lo hi : ℚ)
    (hl : 0 < lo) (hu : 0 < hi) (hzl : |z lo| < 1) (hzu : |z hi| < 1)
    (hx : (logHi lo : ℝ) ≤ x ∧ x ≤ (logLo hi : ℝ)) :
    (lo : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (hi : ℝ) := by
  have hll := (log_bounds lo hl hzl).2.trans hx.1
  have huu := hx.2.trans (log_bounds hi hu hzu).1
  have hl' : (0 : ℝ) < lo := by exact_mod_cast hl
  have hu' : (0 : ℝ) < hi := by exact_mod_cast hu
  constructor
  · simpa [Real.exp_log hl'] using Real.exp_le_exp.mpr hll
  · simpa [Real.exp_log hu'] using Real.exp_le_exp.mpr huu

def factorLower : List ℚ := [974/1000,1279/1000,1146/1000,955/1000,814/1000,931/1000,956/1000]
def factorUpper : List ℚ := [977/1000,1284/1000,1150/1000,959/1000,817/1000,934/1000,960/1000]

theorem factor_intervals : ∀ i < 7,
    ((factorLower[i]! : ℚ) : ℝ) ≤ tmm 1 20 i ∧ tmm 1 20 i ≤ ((factorUpper[i]! : ℚ) : ℝ) := by
  intro i hi
  have h := default_log_bounds.2 i hi
  interval_cases i <;>
    (apply exp_interval _ _ _ (by norm_num [factorLower]) (by norm_num [factorUpper])
      (by norm_num [factorLower, z]) (by norm_num [factorUpper, z])
     norm_num [factorLower, factorUpper, logLo, logHi, poly, err, z] at h ⊢
     constructor <;> linarith)

def within (actual : List ℚ) (tol : ℚ) : Prop :=
  actual.length = 7 ∧ ∀ i < 7, |((actual[i]! : ℚ) : ℝ) - tmm 1 20 i| ≤ (tol : ℝ)

theorem r1_coarse : within edgeFactors (1/40) := by
  constructor
  · exact artifact_lengths.1
  · intro i hi
    have h := factor_intervals i hi
    interval_cases i <;>
      norm_num [factorLower, factorUpper, edge_values] at h ⊢ <;> rw [abs_le] <;> constructor <;> linarith

theorem r2_coarse : within rnaFactors (1/40) := by
  constructor
  · exact artifact_lengths.2
  · intro i hi
    have h := factor_intervals i hi
    interval_cases i <;>
      norm_num [factorLower, factorUpper, rna_values] at h ⊢ <;> rw [abs_le] <;> constructor <;> linarith

theorem r1_fine_counterexample :
    |((edgeFactors[2]! : ℚ) : ℝ) - tmm 1 20 2| > (tolerance : ℝ) := by
  have h := sample3_gt
  have hv' : ((edgeFactors[2]! : ℚ) : ℝ) < 1126/1000 := by norm_num [edge_values]
  have ha := neg_le_abs (((edgeFactors[2]! : ℚ) : ℝ) - tmm 1 20 2)
  norm_num [tolerance] at *
  linarith

theorem r2_fine_counterexample :
    |((rnaFactors[2]! : ℚ) : ℝ) - tmm 1 20 2| > (tolerance : ℝ) := by
  have h := sample3_gt
  have hv' : ((rnaFactors[2]! : ℚ) : ℝ) < 1128/1000 := by norm_num [rna_values]
  have ha := neg_le_abs (((rnaFactors[2]! : ℚ) : ℝ) - tmm 1 20 2)
  norm_num [tolerance] at *
  linarith

theorem r2_literal_counterexample :
    tmm 3 10 1 - ((rnaFactors[1]! : ℚ) : ℝ) > (1/40 : ℝ) := by
  have h0 := bound_literal_0
  have h1 := bound_literal_1
  have h2 := bound_literal_2
  have h3 := bound_literal_3
  have h4 := bound_literal_4
  have h5 := bound_literal_5
  have h6 := bound_literal_6
  have hx : (34/100 : ℝ) < normLog 3 10 1 := by
    simp only [normLog, List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
    norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
    linarith [h0.2,h1.1,h1.2,h2.2,h3.2,h4.2,h5.2,h6.2]
  have he := Real.add_one_le_exp (normLog 3 10 1)
  have hv' : ((rnaFactors[1]! : ℚ) : ℝ) < 128/100 := by norm_num [rna_values]
  unfold tmm
  linarith

#print axioms r1_coarse
#print axioms r2_coarse
#print axioms r2_literal_counterexample
end Verify
