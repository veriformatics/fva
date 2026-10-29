import Proofs.Cases

namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every strict fixture obeys the independent format and end conditions. -/
theorem strict_inputs_valid :
    strictBlocks.all (fun (_, b, cap) => b.valid && b.decode.length ≤ cap) = true := by
  decide

/-- Exact bounded claim; NOT a theorem quantifying over arbitrary caller memory
    or all possible buffers. A case fixes memory outside input to 0xa5 in the
    caller band, except for the module's initial data below that band. -/
theorem bounded_artifact_checks : cases.all Case.certify = true := by
  native_decide

theorem each_case_certified (c : Case) (h : c ∈ cases) : c.certify = true := by
  exact List.all_eq_true.mp bounded_artifact_checks c h

/-- The buffer-band limit rules out 32-bit overflow in a single length-extension
    accumulator: each byte adds at most 255, plus at most 19 from the token.
    This arithmetic lemma does not establish a decoder loop invariant. -/
theorem extension_accumulator_fits (n acc : Nat) (hn : n ≤ 1966080)
    (ha : acc ≤ 255*n+19) : acc < 4294967296 := by omega

end Verification

#print axioms Artifact.instruction_decode
#print axioms Verification.strict_inputs_valid
#print axioms Verification.bounded_artifact_checks
#print axioms Verification.each_case_certified
#print axioms Verification.extension_accumulator_fits
#print axioms LZ4.copyMatch_length
#print axioms LZ4.Sequence.decode_length
#print axioms LZ4.valid_implies_relaxed
#print axioms LZ4.sequencesOK_head
