import Proofs.DataBase
namespace TMM
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000

theorem matrix_shape : counts.length = 454 ∧ (∀ row ∈ counts, row.length = 7 ∧ row.sum > 0) := by
  have h : counts.all (fun row => row.length == 7 && 0 < row.sum) = true := by decide_cbv
  refine ⟨by decide +kernel, ?_⟩
  simpa only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h

theorem quartiles : (List.range 7).map (quartile counts) = [4,2,2,3,5,3,3] := by
  decide_cbv

end TMM
