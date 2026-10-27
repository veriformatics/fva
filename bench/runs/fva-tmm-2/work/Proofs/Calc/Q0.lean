import Proofs.Data
import FVA.Lifted

namespace Proofs
open Bounds Model
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lib_0 : lib Data.counts 0 = 1261 := by kernel_rfl
theorem sort_0 : (col (active Data.counts) 0).mergeSort (· ≤ ·) = Data.sorted0 := by
  have hp : Data.sorted0.Perm (col (active Data.counts) 0) := by decide +kernel
  have hs : Data.sorted0.SortedLE := by decide +kernel
  exact ((List.mergeSort_perm _ _).trans hp.symm).eq_of_pairwise' 
    (List.pairwise_mergeSort' (· ≤ ·) _) hs.pairwise
theorem uq_0 : uq Data.counts 0 = (4 / 1261 : ℚ) := by
  unfold uq
  rw [sort_0, lib_0]
  kernel_rfl

end Proofs
