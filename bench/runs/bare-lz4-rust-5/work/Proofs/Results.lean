import Proofs.Artifact

namespace Verification
open Wasm Artifact

set_option maxRecDepth 100000

/-- A universal fact about actual decoder instructions: an empty compressed
    buffer is rejected without any memory access, for arbitrary memory. -/
theorem zero_length_rejected (src dst cap : Nat) (m : Memory) :
    ∃ s, run decoder 5 (initial src dst 0 cap m) = .returned 4294967295 s ∧
      s.mem = m ∧ s.accesses = [] := by
  exact ⟨_, rfl, rfl, rfl⟩

end Verification
