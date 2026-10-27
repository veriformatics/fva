import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_5 : lib Data.counts 5 = 1136 := by kernel_rfl
theorem sort_5 : (col (active Data.counts) 5).mergeSort (· ≤ ·) = Data.sorted5 := by
  have hp : Data.sorted5.Perm (col (active Data.counts) 5) := by decide +kernel
  have hs : Data.sorted5.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_5 : uq Data.counts 5 = (3 / 1136 : ℚ) := by
  unfold uq
  rw [sort_5, lib_5]
  kernel_rfl

end Proofs
