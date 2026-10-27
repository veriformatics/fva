import Proofs.Model

namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem edge_exact_bytes : edgeBytes =
  "0.99099942459293067\n1.2772984068792248\n1.1253076397204775\n0.95358597286325431\n0.81337534218434382\n0.92968280356711641\n0.97359269251916547\n" := by rfl

theorem rna_exact_bytes : rnaBytes =
  "0.9816880015656044\n1.2793096928626835\n1.1270795948647565\n0.9550875280917844\n0.8146561160553638\n0.9311467198937998\n0.9751257511415794\n" := by rfl

theorem edge_decoded : edge = [99099942459293067/10^17,12772984068792248/10^16,
  11253076397204775/10^16,95358597286325431/10^17,81337534218434382/10^17,
  92968280356711641/10^17,97359269251916547/10^17] := by decide +kernel

theorem rna_decoded : rna = [9816880015656044/10^16,12793096928626835/10^16,
  11270795948647565/10^16,9550875280917844/10^16,8146561160553638/10^16,
  9311467198937998/10^16,9751257511415794/10^16] := by decide +kernel

theorem factor_file_lengths : edge.length = 7 ∧ rna.length = 7 := by
  rw [edge_decoded, rna_decoded]; decide +kernel

-- Stronger than failure at 10 decimal places: every discrepancy exceeds 0.001.
theorem R3_all_seven_gaps : ∀ i ∈ List.range 7,
    (1 : ℚ) / 1000 < |edge[i]! - rna[i]!| := by
  rw [edge_decoded, rna_decoded]; decide +kernel

theorem R3_first_gap_exact : edge[0]! - rna[0]! =
    (931142302732627 : ℚ) / 10^17 := by
  rw [edge_decoded, rna_decoded]; decide +kernel

-- This sufficient numeric contradiction is used for R1/R2 below.
theorem edge_pair_gap : edge[2]! + (1 : ℚ)/10^10 <
    (1181 : ℚ)/1000 * (edge[3]! - (1 : ℚ)/10^10) := by
  rw [edge_decoded]; decide +kernel

theorem rna_pair_gap : rna[2]! + (1 : ℚ)/10^10 <
    (1181 : ℚ)/1000 * (rna[3]! - (1 : ℚ)/10^10) := by
  rw [rna_decoded]; decide +kernel

end Verification
