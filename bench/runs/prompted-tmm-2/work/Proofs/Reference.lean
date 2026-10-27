import Proofs.Quartiles
import Mathlib.Tactic.IntervalCases
namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem reference_correct : referenceOK counts 3 := by
  have ht : (List.range 7).map (fun j => (total counts j : ℚ)) =
      [1261,621,755,1097,1916,1136,1219] := by
    change [(total counts 0 : ℚ), (total counts 1 : ℚ), (total counts 2 : ℚ),
      (total counts 3 : ℚ), (total counts 4 : ℚ), (total counts 5 : ℚ),
      (total counts 6 : ℚ)] = _
    rw [total0_correct,total1_correct,total2_correct,total3_correct,
      total4_correct,total5_correct,total6_correct]
    norm_num
  have hz : (List.range 7).map (fun j => quartile counts j / total counts j) =
      List.zipWith (fun a b : ℚ => a/b) ((List.range 7).map (quartile counts))
        ((List.range 7).map (fun j => (total counts j : ℚ))) := by
    simp only [List.zipWith_map, List.zipWith_self]
  have hq : (List.range 7).map (fun j => quartile counts j / total counts j) =
      [(4/1261 : ℚ), (2/621 : ℚ), (2/755 : ℚ), (3/1097 : ℚ),
       (5/1916 : ℚ), (3/1136 : ℚ), (3/1219 : ℚ)] := by
    rw [hz, quartiles, ht]
    decide_cbv
  unfold referenceOK
  rw [hq]
  constructor
  · norm_num
  · intro j hj
    have hj' : j < 7 := List.mem_range.mp hj
    interval_cases j <;> norm_num
end TMM
