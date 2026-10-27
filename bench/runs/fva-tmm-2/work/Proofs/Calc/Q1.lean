import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_1 : lib Data.counts 1 = 621 := by kernel_rfl
theorem sort_1 : (col (active Data.counts) 1).mergeSort (· ≤ ·) = Data.sorted1 := by
  have hp : Data.sorted1.Perm (col (active Data.counts) 1) := by decide +kernel
  have hs : Data.sorted1.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_1 : uq Data.counts 1 = (2 / 621 : ℚ) := by
  unfold uq
  rw [sort_1, lib_1]
  kernel_rfl

end Proofs
