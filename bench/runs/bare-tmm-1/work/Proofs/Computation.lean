import Proofs.Bounds

namespace Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- These exact finite computations use native_decide; the trust boundary is audited.
run_elab IO.eprintln "CHECKING dimensions"
theorem dimensions : counts.length = 454 ∧ (∀ r ∈ counts, r.length = 7) := by native_decide
run_elab IO.eprintln "CHECKING no_zero_rows"
theorem no_zero_rows : ∀ r ∈ counts, r.sum > 0 := by native_decide
run_elab IO.eprintln "CHECKING libraries"
theorem libraries : (List.range 7).map lib = [1261,621,755,1097,1916,1136,1219] := by native_decide
run_elab IO.eprintln "CHECKING quartiles"
theorem quartiles : (List.range 7).map quartile = [4,2,2,3,5,3,3] := by native_decide
run_elab IO.eprintln "CHECKING reference_is_fourth"
theorem reference_is_fourth : reference = 3 := by native_decide

run_elab IO.eprintln "CHECKING no_reference_fallback"
theorem no_reference_fallback : ∀ j ∈ List.range 7, (1 : ℚ) / 10^20 < uq j := by native_decide

run_elab IO.eprintln "CHECKING count_format"
theorem count_format : ∀ row ∈ lines countsBytes, ∀ cell ∈ row.splitOn '\t',
    cell ≠ [] ∧ (∀ c ∈ cell, '0' ≤ c ∧ c ≤ '9') := by native_decide

run_elab IO.eprintln "CHECKING pair3_population"
theorem pair3_population : (positivePairs 2).length = 205 := by native_decide
run_elab IO.eprintln "CHECKING gene451_counts"
theorem gene451_counts : (counts[450]!)[2]! = 5 ∧ (counts[450]!)[3]! = 10 := by native_decide
run_elab IO.eprintln "CHECKING gene451_exact_rank"
theorem gene451_exact_rank : twiceRank mLt mEq (positivePairs 2) (5,10) = 114 := by native_decide

def defaultPairs : List Pair := [(4,4),(2,2),(2,2),(3,4),(1,1),(2,3),(4,4),(3,4),(5,9),(1,1),(2,3),(2,3),(3,3),(1,1),(4,6),(4,5),(4,7),(1,1),(2,2),(2,2),(1,1),(1,1),(1,1),(1,1),(2,3),(2,3),(3,3),(2,2),(1,1),(1,1),(3,4),(3,3),(1,1),(4,4),(2,2),(2,2),(5,6),(2,2),(1,1),(1,1),(2,2),(1,1),(1,1),(1,1),(3,3),(2,2),(1,1),(7,8),(4,6),(2,3),(4,5),(3,5),(1,1),(1,1),(2,2),(1,1),(1,1),(2,2),(1,1),(1,1),(4,5),(2,3),(2,2),(3,3),(6,9),(4,5),(1,1),(5,8),(1,1),(2,3),(1,1),(1,1),(1,1),(5,7),(6,6),(2,2)]
run_elab IO.eprintln "CHECKING default_selection"
theorem default_selection : selected 2 1 20 = defaultPairs := by native_decide

run_elab IO.eprintln "CHECKING default_positive"
theorem default_positive : ∀ p ∈ defaultPairs, 0 < ratio 2 p ∧ 0 ≤ weight 2 p := by native_decide
run_elab IO.eprintln "CHECKING default_weight_positive"
theorem default_weight_positive : 0 < (defaultPairs.map (weight 2)).sum := by native_decide
run_elab IO.eprintln "CHECKING default_rational_bound"
theorem default_rational_bound : (181 : ℚ)/1000 <
    (defaultPairs.map (fun p => weight 2 p * logLower (ratio 2 p))).sum /
    (defaultPairs.map (weight 2)).sum := by native_decide

def literalPairs : List Pair := [(2,2),(2,2),(3,4),(2,3),(3,4),(2,3),(2,3),(3,3),(2,2),(2,2),(2,3),(2,3),(3,3),(2,2),(3,4),(3,3),(2,2),(2,2),(2,2),(2,2),(3,3),(2,2),(2,3),(2,2),(2,2),(2,3),(2,2),(3,3),(2,3),(2,2)]
run_elab IO.eprintln "CHECKING literal_selection"
theorem literal_selection : selected 2 3 10 = literalPairs := by native_decide

run_elab IO.eprintln "CHECKING literal_positive"
theorem literal_positive : ∀ p ∈ literalPairs, 0 < ratio 2 p ∧ 0 ≤ weight 2 p := by native_decide
run_elab IO.eprintln "CHECKING literal_weight_positive"
theorem literal_weight_positive : 0 < (literalPairs.map (weight 2)).sum := by native_decide
run_elab IO.eprintln "CHECKING literal_rational_bound"
theorem literal_rational_bound : (181 : ℚ)/1000 <
    (literalPairs.map (fun p => weight 2 p * logLower (ratio 2 p))).sum /
    (literalPairs.map (weight 2)).sum := by native_decide

end Verification
