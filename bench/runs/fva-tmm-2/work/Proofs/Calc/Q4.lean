import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_4 : lib Data.counts 4 = 1916 := by kernel_rfl
theorem sort_4 : (col (active Data.counts) 4).mergeSort (· ≤ ·) = Data.sorted4 := by
  have hp : Data.sorted4.Perm (col (active Data.counts) 4) := by decide +kernel
  have hs : Data.sorted4.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_4 : uq Data.counts 4 = (5 / 1916 : ℚ) := by
  unfold uq
  rw [sort_4, lib_4]
  kernel_rfl

end Proofs
