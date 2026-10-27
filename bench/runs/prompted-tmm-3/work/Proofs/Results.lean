import Proofs.Bounds
namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem log_factor_ratio (a b : Nat) :
    Real.log (factor 0 a b / factor 3 a b) = raw 0 a b := by
  unfold factor
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, Real.log_exp]
  simp [raw, reference_is_four]

theorem necessary (a b : Nat) (h : raw 0 a b ≤ 3/125) :
    122 * factor 0 a b ≤ 125 * factor 3 a b := by
  have hx : 0 < factor 0 a b := Real.exp_pos _
  have hy : 0 < factor 3 a b := Real.exp_pos _
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  rw [log_factor_ratio, inv_div] at hl
  have hq : 1 - (3/125 : ℝ) ≤ factor 3 a b / factor 0 a b := by linarith
  have hh := (le_div_iff₀ hx).1 hq
  linarith

theorem artifact_values : edge = [99099942459293067/10^17,12772984068792248/10^16,
    11253076397204775/10^16,95358597286325431/10^17,81337534218434382/10^17,
    92968280356711641/10^17,97359269251916547/10^17] ∧
    rna = [9816880015656044/10^16,12793096928626835/10^16,11270795948647565/10^16,
    9550875280917844/10^16,8146561160553638/10^16,9311467198937998/10^16,
    9751257511415794/10^16] := by decide +kernel

theorem separation :
    125 * (((edge[3]! : ℚ) : ℝ) + tolerance) < 122 * (((edge[0]! : ℚ) : ℝ) - tolerance) ∧
    125 * (((rna[3]! : ℚ) : ℝ) + tolerance) < 122 * (((rna[0]! : ℚ) : ℝ) - tolerance) := by
  rw [artifact_values.1, artifact_values.2]
  norm_num [tolerance]

theorem fails (xs : List ℚ) (a b : Nat) (hb : raw 0 a b ≤ 3/125)
    (hs : 125 * (((xs[3]! : ℚ) : ℝ) + tolerance) <
      122 * (((xs[0]! : ℚ) : ℝ) - tolerance)) : ¬ Meets xs a b := by
  intro h
  have h0 := (abs_le.1 (h 0 (by norm_num))).2
  have h3 := (abs_le.1 (h 3 (by norm_num))).1
  have hn := necessary a b hb
  linarith

theorem R1 : ¬ Meets edge 1 20 := fails edge 1 20 raw_bound separation.1
theorem R2 : ¬ Meets rna 1 20 := fails rna 1 20 raw_bound separation.2
theorem R2_literal : ¬ Meets rna 3 10 := fails rna 3 10 literal_raw_bound separation.2

theorem R3_gap : (9/1000 : ℚ) < |edge[0]! - rna[0]!| := by
  rw [artifact_values.1, artifact_values.2]
  norm_num

theorem R3 : ¬ (∀ i < 7, |edge[i]! - rna[i]!| ≤ (1/10000000000 : ℚ)) := by
  intro h
  have h0 := h 0 (by decide)
  linarith [R3_gap]
end Verification
