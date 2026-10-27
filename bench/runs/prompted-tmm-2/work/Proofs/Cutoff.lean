import Proofs.DataBase
import Mathlib.Tactic.FinCases
namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem pairs_pos (x : Matrix) (j r : Nat) (p : Nat × Nat)
    (hp : p ∈ pairs x j r) : 0 < p.1 ∧ 0 < p.2 := by
  have h := (List.mem_filter.mp hp).2
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

private theorem lower_log {x : ℝ} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  simpa only [one_div] using (by linarith : 1 - x⁻¹ ≤ Real.log x)

private theorem cutoff_of_bounds (a b no nr : ℝ) (h1 : 1 ≤ a) (h2 : 1 ≤ b)
    (hn : 0 < no) (hn' : no ≤ 2000) (hr : 0 < nr) (hr' : nr ≤ 2000) :
    (-10000000000 : ℝ) < (Real.log (a/no) + Real.log (b/nr)) / (2*Real.log 2) := by
  have ha : (1/2000 : ℝ) ≤ a/no := (le_div_iff₀ hn).2 (by nlinarith)
  have hb : (1/2000 : ℝ) ≤ b/nr := (le_div_iff₀ hr).2 (by nlinarith)
  have hl := lower_log (show (0 : ℝ) < 1/2000 by norm_num)
  have hla := Real.log_le_log (show (0 : ℝ) < 1/2000 by norm_num) ha
  have hlb := Real.log_le_log (show (0 : ℝ) < 1/2000 by norm_num) hb
  have hl2 := lower_log (show (0 : ℝ) < 2 by norm_num)
  norm_num at hl hl2
  have hd : 0 < 2 * Real.log 2 := by linarith
  apply (lt_div_iff₀ hd).2
  linarith

theorem cutoff_irrelevant (j : Fin 7) (p : Nat × Nat) (hp : p ∈ pairs counts j.val 3) :
    (-10000000000 : ℝ) <
      (Real.log ((p.1 : ℝ) / total counts j.val) +
       Real.log ((p.2 : ℝ) / total counts 3)) / (2 * Real.log 2) := by
  have hn : 0 < total counts j.val ∧ total counts j.val ≤ 2000 := by
    fin_cases j <;> norm_num [total0_correct,total1_correct,total2_correct,
      total3_correct,total4_correct,total5_correct,total6_correct]
  have hp' := pairs_pos counts j.val 3 p hp
  apply cutoff_of_bounds
  · exact_mod_cast (Nat.succ_le_of_lt hp'.1)
  · exact_mod_cast (Nat.succ_le_of_lt hp'.2)
  · exact Nat.cast_pos.mpr hn.1
  · exact Nat.cast_le.mpr hn.2
  · norm_num [total3_correct]
  · norm_num [total3_correct]
end TMM
