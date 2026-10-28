import Proofs.Proof
namespace Proofs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem empty_zero_holds : empty_zero := by
  apply checked_case (fuel := 500)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem empty_room_holds : empty_room := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem one_literal_holds : one_literal := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem extended_literals_holds : extended_literals := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem overlap_match_holds : overlap_match := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem extended_match_holds : extended_match := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem zero_offset_holds : zero_offset := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem source_at_end_holds : source_at_end := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem destination_at_end_holds : destination_at_end := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem reject_no_input_holds : reject_no_input := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem reject_zero_capacity_holds : reject_zero_capacity := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

theorem reject_past_offset_holds : reject_past_offset := by
  apply checked_case (fuel := 3000)
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · decide +kernel
  · decide +kernel

end Proofs
