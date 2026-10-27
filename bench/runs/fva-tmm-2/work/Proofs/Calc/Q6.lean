import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_6 : lib Data.counts 6 = 1219 := by kernel_rfl
theorem sort_6 : (col (active Data.counts) 6).mergeSort (· ≤ ·) = Data.sorted6 := by
  have hp : Data.sorted6.Perm (col (active Data.counts) 6) := by decide +kernel
  have hs : Data.sorted6.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_6 : uq Data.counts 6 = (3 / 1219 : ℚ) := by
  unfold uq
  rw [sort_6, lib_6]
  kernel_rfl

end Proofs
