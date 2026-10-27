import Proofs.Bounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

theorem no_fit (f : List ℚ)
    (hfirst : (981 : ℝ) / 1000 < (f[0]! : ℝ))
    (hfourth : (f[3]! : ℝ) < 956 / 1000) :
    ¬ FitsPair f (1 / 10^10) := by
  rintro ⟨first, fourth, ⟨scale, hs, h₁, h₄⟩, hfirst', hfourth'⟩
  have hraw := rawFirst_upper
  have hrel : first < (41 / 40) * fourth := by
    rw [h₁, h₄]
    exact mul_lt_mul_of_pos_right hraw hs
  have ha := (abs_le.mp hfirst').1
  have hb := (abs_le.mp hfourth').2
  linarith

theorem R1_failure : ¬ FitsPair edge (1 / 10^10) := by
  apply no_fit
  all_goals norm_num [edge, Artifact.edge]

theorem R2_failure : ¬ FitsPair rna (1 / 10^10) := by
  apply no_fit
  all_goals norm_num [rna, Artifact.rna]

theorem R3_failure : |edge[0]! - rna[0]!| > (1 : ℚ) / 10^10 := by
  norm_num [edge, rna, Artifact.edge, Artifact.rna]

theorem R3_gap : edge[0]! - rna[0]! = (931142302732627 : ℚ) / 10^17 := by
  norm_num [edge, rna, Artifact.edge, Artifact.rna]

end Verification
