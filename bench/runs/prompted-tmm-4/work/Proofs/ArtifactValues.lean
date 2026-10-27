import Proofs.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

theorem edge_first : edge[0]! = (99099942459293067 : ℚ) / 100000000000000000 := by cbv
theorem rna_first : rna[0]! = (9816880015656044 : ℚ) / 10000000000000000 := by cbv
theorem output_shape : edge.length = 7 ∧ rna.length = 7 := by cbv

theorem R3_failure : tolerance < |edge[0]! - rna[0]!| := by
  rw [edge_first, rna_first]
  norm_num [tolerance]

theorem first_difference : edge[0]! - rna[0]! =
    (931142302732627 : ℚ) / 100000000000000000 := by
  rw [edge_first, rna_first]
  norm_num

end Verification
