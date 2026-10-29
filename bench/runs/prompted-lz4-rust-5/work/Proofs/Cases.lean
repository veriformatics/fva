import Proofs.Traces
namespace Verification

theorem samples_artifact : Samples.all.all agrees = true := by
  simp only [Samples.all, List.all_cons, List.all_nil,
    run_empty_block, run_literal_A, run_literals_2, run_literals_3,
    run_literals_4, run_literals_7, run_literals_8, run_literals_15,
    run_literals_16, run_literals_17, run_literals_32, run_literals_33,
    run_offset_one, run_offset_two, run_match_extension, run_fast_overlap,
    run_fast_wide18, run_slow_wide32, run_slow_wide64, run_slow_bulkcopy,
    run_no_input, run_zero_offset, run_offset_outside, run_truncated_literal_length,
    run_truncated_match_length, run_small_literal_capacity, run_small_match_capacity,
    run_relaxed_end, Bool.and_self]
end Verification
