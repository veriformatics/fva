import Proofs.Numeric
import Proofs.ArtifactValues

namespace Verification

theorem first_TMM_lt : tmm 0 < (98 : ℝ) / 100 := by
  have hx : raw 0 - ((List.range 7).map raw).sum / 7 ≤ -(24 : ℝ) / 1000 := by
    have h0 := raw_0.2
    have h1 := raw_1.1
    have h2 := raw_2.1
    have h3 := raw_3.1
    have h4 := raw_4.1
    have h5 := raw_5.1
    have h6 := raw_6.1
    norm_num at h0 h1 h2 h3 h4 h5 h6
    norm_num [show List.range 7 = [0,1,2,3,4,5,6] from by decide]
    linarith
  have he := Real.add_one_le_exp ((24 : ℝ) / 1000)
  have hb : Real.exp (-(24 : ℝ) / 1000) < (98 : ℝ) / 100 := by
    rw [neg_div, Real.exp_neg]
    apply (inv_lt_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  exact (Real.exp_le_exp.mpr hx).trans_lt hb

theorem R1_failure : ¬ Meets edge := by
  intro h
  have h0 := (abs_le.mp (h 0 (by decide))).2
  have ho : (edge[0]! : ℝ) = (99099942459293067 : ℝ) / 100000000000000000 := by
    rw [edge_first]
    norm_num
  have ht := first_TMM_lt
  norm_num [tolerance] at h0
  linarith

theorem R2_failure : ¬ Meets rna := by
  intro h
  have h0 := (abs_le.mp (h 0 (by decide))).2
  have ho : (rna[0]! : ℝ) = (9816880015656044 : ℝ) / 10000000000000000 := by
    rw [rna_first]
    norm_num
  have ht := first_TMM_lt
  norm_num [tolerance] at h0
  linarith

end Verification
