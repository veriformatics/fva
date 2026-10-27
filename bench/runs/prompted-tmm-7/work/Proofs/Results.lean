import Proofs.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verify

theorem input_encoding :
    ((lines countsBytes).mapM fun (r : List ℕ) => (r.splitOn 9).mapM digits).isSome ∧
    countsBytes.getLast? = some 10 ∧ edgeBytes.getLast? = some 10 ∧ rnaBytes.getLast? = some 10 := by decide +kernel

theorem artifact_lengths : edgeFactors.length = 7 ∧ rnaFactors.length = 7 := by decide +kernel

theorem edge_values : edgeFactors = [(99099942459293067/100000000000000000 : ℚ), (1596623008599031/1250000000000000 : ℚ), (450123055888191/400000000000000 : ℚ), (95358597286325431/100000000000000000 : ℚ), (40668767109217191/50000000000000000 : ℚ), (92968280356711641/100000000000000000 : ℚ), (97359269251916547/100000000000000000 : ℚ)] := by decide +kernel

theorem rna_values : rnaFactors = [(2454220003914011/2500000000000000 : ℚ), (2558619385725367/2000000000000000 : ℚ), (2254159189729513/2000000000000000 : ℚ), (2387718820229461/2500000000000000 : ℚ), (4073280580276819/5000000000000000 : ℚ), (4655733599468999/5000000000000000 : ℚ), (4875628755707897/5000000000000000 : ℚ)] := by decide +kernel

theorem first_difference :
    edgeFactors[0]! - rnaFactors[0]! = (931142302732627 / 100000000000000000 : ℚ) := by decide +kernel

theorem r3_counterexample : |rnaFactors[0]! - edgeFactors[0]!| > tolerance := by decide +kernel

theorem r3_fails : ¬ agrees rnaBytes := by
  intro ⟨es, rs, he, hr, _, _, h⟩
  have he' : edgeFactors = es := by simp [edgeFactors, he]
  have hr' : rnaFactors = rs := by simp [rnaFactors, hr]
  have ht := h 0 (by decide)
  rw [← he', ← hr'] at ht
  exact (not_le.mpr r3_counterexample) ht

#print axioms r3_fails
end Verify
