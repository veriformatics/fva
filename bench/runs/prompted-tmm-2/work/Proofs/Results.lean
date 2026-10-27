import Proofs.MeanCertificates
import Proofs.Reference
import Proofs.Artifact

namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem first_factor_upper : factor counts 0 3 < (977/1000 : ℝ) := by
  have h0 := mean0_bounds
  have h1 := mean1_bounds
  have h2 := mean2_bounds
  have h3 := mean3_bounds
  have h4 := mean4_bounds
  have h5 := mean5_bounds
  have h6 := mean6_bounds
  have hc : meanLog (terms counts 0 3) -
      ((List.range 7).map fun k => meanLog (terms counts k 3)).sum / 7 < (-24/1000 : ℝ) := by
    norm_num only [List.range_succ, List.range_zero, List.map_cons, List.map_append,
      List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
      mean0_correct,mean1_correct,mean2_correct,mean3_correct,
      mean4_correct,mean5_correct,mean6_correct]
    norm_num at h0 h1 h2 h3 h4 h5 h6
    linarith
  have hl := log87
  norm_num at hl
  have hlog : (-24/1000 : ℝ) < Real.log (977/1000 : ℝ) := by linarith [hl.1]
  unfold factor
  calc
    Real.exp _ < Real.exp (Real.log (977/1000 : ℝ)) := Real.exp_lt_exp.mpr (lt_trans hc hlog)
    _ = _ := Real.exp_log (by norm_num)

-- These two failures concern exact mathematical TMM with the defaults in Spec.
-- The scale 10^17 connects the real values to the decimal bytes in Artifact.
theorem R1_exact_counterexample :
    (1/1000 : ℝ) < |(Artifact.edge[0]! : ℝ) / 10^17 - factor counts 0 3| := by
  have h := first_factor_upper
  have he : (Artifact.edge[0]! : ℝ) / 10^17 = (99099942459293067/100000000000000000 : ℝ) := by
    norm_num [Artifact.edge]
  rw [he, abs_of_pos (by linarith)]
  linarith

theorem R2_exact_counterexample :
    (1/1000 : ℝ) < |(Artifact.rna[0]! : ℝ) / 10^17 - factor counts 0 3| := by
  have h := first_factor_upper
  have he : (Artifact.rna[0]! : ℝ) / 10^17 = (98168800156560440/100000000000000000 : ℝ) := by
    norm_num [Artifact.rna]
  rw [he, abs_of_pos (by linarith)]
  linarith
end TMM
