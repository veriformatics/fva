import Proofs.Data

namespace Verification

theorem library_bounds : ∀ i ∈ List.range 7, 0 < library i ∧ library i ≤ 2000 := by
  decide +kernel

theorem cutoff_bound (a b n m : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : 0 < n) (hm : 0 < m) (hn' : n ≤ 2000) (hm' : m ≤ 2000) :
    -(10000000000 : ℝ) < (Real.log (a / n) + Real.log (b / m)) / 2 := by
  have ha' : 0 < a := by linarith
  have hb' : 0 < b := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ha' hn)
  have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hb' hm)
  rw [inv_div] at h1 h2
  have h3 : n / a ≤ 2000 := (div_le_iff₀ ha').mpr (by nlinarith)
  have h4 : m / b ≤ 2000 := (div_le_iff₀ hb').mpr (by nlinarith)
  linarith

theorem cutoff_irrelevant (i : Nat) (hi : i ∈ List.range 7)
    (p : Nat × Nat) (hp : p ∈ pairs i) :
    -(10000000000 : ℝ) <
      (Real.log ((p.1 : ℝ) / library i) + Real.log ((p.2 : ℝ) / library refIndex)) / 2 := by
  have hpos : 0 < p.1 ∧ 0 < p.2 := by
    have h := (List.mem_filter.mp hp).2
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
  have hlib := library_bounds i hi
  have href := library_bounds 3 (by decide)
  rw [reference]
  apply cutoff_bound
  · exact_mod_cast hpos.1
  · exact_mod_cast hpos.2
  · exact_mod_cast hlib.1
  · exact_mod_cast href.1
  · exact_mod_cast hlib.2
  · exact_mod_cast href.2

theorem quantiles_above_fallback : ∀ i ∈ List.range 7,
    (1 : ℚ) / 100000000000000000000 < uq i := by
  norm_num [show List.range 7 = [0,1,2,3,4,5,6] from by decide,
    uq_0, uq_1, uq_2, uq_3, uq_4, uq_5, uq_6]

theorem tied_boundary :
    rank2 mLT (pairs 0) (6, 3) = 355 ∧
    rank2 aLT (pairs 0) (13, 8) = 465 ∧ (pairs 0).length = 244 := by
  rw [pairs_0]
  decide +kernel

end Verification
