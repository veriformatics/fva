import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_2 : lib Data.counts 2 = 755 := by kernel_rfl
theorem sort_2 : (col (active Data.counts) 2).mergeSort (· ≤ ·) = Data.sorted2 := by
  have hp : Data.sorted2.Perm (col (active Data.counts) 2) := by decide +kernel
  have hs : Data.sorted2.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_2 : uq Data.counts 2 = (2 / 755 : ℚ) := by
  unfold uq
  rw [sort_2, lib_2]
  kernel_rfl

end Proofs
