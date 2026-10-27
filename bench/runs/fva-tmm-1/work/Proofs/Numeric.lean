import Proofs.LogBounds
import Proofs.Coefficients
import Proofs.Raw0
import Proofs.Raw1
import Proofs.Raw2
import Proofs.Raw3
import Proofs.Raw4
import Proofs.Raw5
import Proofs.Raw6
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs.Numeric

theorem factor0 : ((487763 / 500000) : ℝ) ≤ tmm Witness.matrix 0 3 ∧
    tmm Witness.matrix 0 3 ≤ ((975529 / 1000000) : ℝ) := by
  have ha := log_certificate ((487763 / 500000)) 0 (-24778467/1000000000) (-24778466/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((975529 / 1000000)) 0 (-24775392/1000000000) (-24775391/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((487763 / 500000 : ℚ) : ℝ) ≤ tmm Witness.matrix 0 3 ∧
      tmm Witness.matrix 0 3 ≤ ((975529 / 1000000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 0 3) (487763 / 500000 : ℚ) (975529 / 1000000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor1 : ((640541 / 500000) : ℝ) ≤ tmm Witness.matrix 1 3 ∧
    tmm Witness.matrix 1 3 ≤ ((256217 / 200000) : ℝ) := by
  have ha := log_certificate ((640541 / 500000)) 0 (247705033/1000000000) (247705034/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((256217 / 200000)) 0 (247707375/1000000000) (247707376/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((640541 / 500000 : ℚ) : ℝ) ≤ tmm Witness.matrix 1 3 ∧
      tmm Witness.matrix 1 3 ≤ ((256217 / 200000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 1 3) (640541 / 500000 : ℚ) (256217 / 200000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor2 : ((1147753 / 1000000) : ℝ) ≤ tmm Witness.matrix 2 3 ∧
    tmm Witness.matrix 2 3 ≤ ((286939 / 250000) : ℝ) := by
  have ha := log_certificate ((1147753 / 1000000)) 0 (137806117/1000000000) (137806118/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((286939 / 250000)) 0 (137808731/1000000000) (137808732/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((1147753 / 1000000 : ℚ) : ℝ) ≤ tmm Witness.matrix 2 3 ∧
      tmm Witness.matrix 2 3 ≤ ((286939 / 250000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 2 3) (1147753 / 1000000 : ℚ) (286939 / 250000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor3 : ((95641 / 100000) : ℝ) ≤ tmm Witness.matrix 3 3 ∧
    tmm Witness.matrix 3 3 ≤ ((956413 / 1000000) : ℝ) := by
  have ha := log_certificate ((95641 / 100000)) 0 (-44568588/1000000000) (-44568587/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((956413 / 1000000)) 0 (-44565451/1000000000) (-44565450/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((95641 / 100000 : ℚ) : ℝ) ≤ tmm Witness.matrix 3 3 ∧
      tmm Witness.matrix 3 3 ≤ ((956413 / 1000000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 3 3) (95641 / 100000 : ℚ) (956413 / 1000000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor4 : ((101973 / 125000) : ℝ) ≤ tmm Witness.matrix 4 3 ∧
    tmm Witness.matrix 4 3 ≤ ((815787 / 1000000) : ℝ) := by
  have ha := log_certificate ((101973 / 125000)) 0 (-203605665/1000000000) (-203605664/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((815787 / 1000000)) 0 (-203601988/1000000000) (-203601987/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((101973 / 125000 : ℚ) : ℝ) ≤ tmm Witness.matrix 4 3 ∧
      tmm Witness.matrix 4 3 ≤ ((815787 / 1000000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 4 3) (101973 / 125000 : ℚ) (815787 / 1000000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor5 : ((233109 / 250000) : ℝ) ≤ tmm Witness.matrix 5 3 ∧
    tmm Witness.matrix 5 3 ≤ ((932439 / 1000000) : ℝ) := by
  have ha := log_certificate ((233109 / 250000)) 0 (-69954763/1000000000) (-69954762/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((932439 / 1000000)) 0 (-69951546/1000000000) (-69951545/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((233109 / 250000 : ℚ) : ℝ) ≤ tmm Witness.matrix 5 3 ∧
      tmm Witness.matrix 5 3 ≤ ((932439 / 1000000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 5 3) (233109 / 250000 : ℚ) (932439 / 1000000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound

theorem factor6 : ((958279 / 1000000) : ℝ) ≤ tmm Witness.matrix 6 3 ∧
    tmm Witness.matrix 6 3 ≤ ((479141 / 500000) : ℝ) := by
  have ha := log_certificate ((958279 / 1000000)) 0 (-42616312/1000000000) (-42616311/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hb := log_certificate ((479141 / 500000)) 0 (-42613182/1000000000) (-42613181/1000000000) (by norm_num) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at ha hb
  have h0 := raw0
  have h1 := raw1
  have h2 := raw2
  have h3 := raw3
  have h4 := raw4
  have h5 := raw5
  have h6 := raw6
  have hbound : ((958279 / 1000000 : ℚ) : ℝ) ≤ tmm Witness.matrix 6 3 ∧
      tmm Witness.matrix 6 3 ≤ ((479141 / 500000 : ℚ) : ℝ) := by
    apply exp_bounds (factorLog Witness.matrix 6 3) (958279 / 1000000 : ℚ) (479141 / 500000 : ℚ) (by norm_num) (by norm_num)
    all_goals
      norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero]
      unfold factorLog
      norm_num [List.range_succ, List.sum_cons, List.map_cons, List.sum_nil, List.map_nil]
      linarith [ha.1, ha.2, hb.1, hb.2]
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using hbound
end Proofs.Numeric
