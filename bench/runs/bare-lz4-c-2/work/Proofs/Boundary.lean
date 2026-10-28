import Proofs.Artifact

namespace Verification.Boundary
open Wasm

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Quantified over arbitrary initial byte maps, not just zero-initialized memory.
theorem no_input_any_memory (m : Memory) :
    invoke Artifact.program 50 2 [131072, 262144, 0, 1] m =
      some ⟨4294967295, m, []⟩ := by rfl

theorem zero_capacity_single_byte (m : Memory) :
    invoke Artifact.program 50 2 [131072, 262144, 1, 0] m =
      some ⟨(if byte m 131072 = 0 then 0 else 4294967295), m,
        [⟨false, 131072, 1⟩]⟩ := by rfl

end Verification.Boundary
