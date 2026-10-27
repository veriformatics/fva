import Proofs.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification
-- These are evaluations by the kernel, not native_decide or an oracle.
theorem dimensions : counts.length = 454 ∧ (counts.all (fun r => r.length == 7)) = true := by decide +kernel
theorem libraries : (List.range 7).map lib = [1261,621,755,1097,1916,1136,1219] := by decide +kernel
theorem reference_is_four : reference = 3 := by decide +kernel
theorem lib_zero : lib 0 = 1261 := by
  have h := congrArg (fun xs : List Nat => xs[0]!) libraries
  exact h
theorem lib_three : lib 3 = 1097 := by
  have h := congrArg (fun xs : List Nat => xs[3]!) libraries
  exact h
end Verification
