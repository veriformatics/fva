import Proofs.Witness
import Proofs.ScoreBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs

theorem score0_bounds : ((18/1000 : ℚ) : ℝ) ≤ score matrix 0 3 ∧
    score matrix 0 3 ≤ ((21/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept0, lib0, lib3]
  exact weighted_bounds pairs0 1261 1097 (18/1000) (21/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score1_bounds : ((291/1000 : ℚ) : ℝ) ≤ score matrix 1 3 ∧
    score matrix 1 3 ≤ ((294/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept1, lib1, lib3]
  exact weighted_bounds pairs1 621 1097 (291/1000) (294/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score2_bounds : ((181/1000 : ℚ) : ℝ) ≤ score matrix 2 3 ∧
    score matrix 2 3 ≤ ((184/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept2, lib2, lib3]
  exact weighted_bounds pairs2 755 1097 (181/1000) (184/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score3_bounds : ((-1/1000 : ℚ) : ℝ) ≤ score matrix 3 3 ∧
    score matrix 3 3 ≤ ((2/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept3, lib3, lib3]
  exact weighted_bounds pairs3 1097 1097 (-1/1000) (2/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score4_bounds : ((-161/1000 : ℚ) : ℝ) ≤ score matrix 4 3 ∧
    score matrix 4 3 ≤ ((-158/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept4, lib4, lib3]
  exact weighted_bounds pairs4 1916 1097 (-161/1000) (-158/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score5_bounds : ((-27/1000 : ℚ) : ℝ) ≤ score matrix 5 3 ∧
    score matrix 5 3 ≤ ((-24/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept5, lib5, lib3]
  exact weighted_bounds pairs5 1136 1097 (-27/1000) (-24/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem score6_bounds : ((0/1000 : ℚ) : ℝ) ≤ score matrix 6 3 ∧
    score matrix 6 3 ≤ ((3/1000 : ℚ) : ℝ) := by
  unfold score
  simp only [kept6, lib6, lib3]
  exact weighted_bounds pairs6 1219 1097 (0/1000) (3/1000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem factor_lower : (114/100 : ℝ) < factor matrix 2 := by
  have h0 := score0_bounds
  have h1 := score1_bounds
  have h2 := score2_bounds
  have h3 := score3_bounds
  have h4 := score4_bounds
  have h5 := score5_bounds
  have h6 := score6_bounds
  have he : (132/1000 : ℝ) < score matrix 2 3 -
      ((List.range 7).map (fun k => score matrix k 3)).sum / 7 := by
    norm_num [List.range_succ, List.map_cons, List.sum_cons] at *
    linarith
  have hs := series_bounds (57/50) (by norm_num) 10
  have hu : series (57/50) 10 + remainder (57/50) 10 < (132/1000 : ℚ) := by decide +kernel
  have hlog : Real.log (114/100 : ℝ) < 132/1000 := by
    have huR : (((series (57/50) 10 + remainder (57/50) 10 : ℚ)) : ℝ) < ((132/1000 : ℚ) : ℝ) := Rat.cast_lt.mpr hu
    have hh := lt_of_le_of_lt hs.2 huR
    norm_num at hh ⊢
    exact hh
  unfold factor
  rw [reference_eq]
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 114/100)).mp (hlog.trans he)

end Proofs
