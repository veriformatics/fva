import Proofs.Artifact

namespace Verification
open Wasm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- The result is the raw i32 word; 4294967295 represents -1.
theorem zero_capacity (m : Memory) (src dst n : Nat)
    (hs : 0 < src) (hm : src < 2097152) :
    execute Artifact.decoder m src dst n 0 =
      some (if n = 1 ∧ (m src).val = 0 then 0 else 4294967295,
            if n = 1 then [src] else []) := by
  have hz : src ≠ 0 := by omega
  by_cases hn : n = 1
  · subst n
    by_cases hb : (m src).val = 0
    · simp [execute, Artifact.decoder, eval, step, binary, signed, hz, hm, hb]
    · simp [execute, Artifact.decoder, eval, step, binary, signed, hz, hm, hb]
  · simp [execute, Artifact.decoder, eval, step, binary, signed, hz, hn]

theorem zero_source_size (m : Memory) (src dst cap : Nat)
    (hs : src ≠ 0) (hc : 0 < cap) (hc32 : cap < 2147483648) :
    execute Artifact.decoder m src dst 0 cap = some (4294967295, []) := by
  have hcz : cap ≠ 0 := by omega
  have hcn : ¬ (cap : Int) < 0 := by omega
  simp [execute, Artifact.decoder, eval, step, binary, signed, hs, hcz, hc32, hcn]

#print axioms zero_capacity
#print axioms zero_source_size
end Verification
