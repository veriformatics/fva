import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_3 : lib Data.counts 3 = 1097 := by kernel_rfl
theorem sort_3 : (col (active Data.counts) 3).mergeSort (· ≤ ·) = Data.sorted3 := by
  have hp : Data.sorted3.Perm (col (active Data.counts) 3) := by decide +kernel
  have hs : Data.sorted3.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_3 : uq Data.counts 3 = (3 / 1097 : ℚ) := by
  unfold uq
  rw [sort_3, lib_3]
  kernel_rfl

end Proofs
