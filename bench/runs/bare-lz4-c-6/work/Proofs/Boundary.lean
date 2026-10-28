import Proofs.Artifact

namespace Boundary
open Wasm Artifact

-- Observe return value, every memory access, and the complete final memory.
def observe (s : Option State) : Option (Nat × List Access × Memory) := do
  let s ← s
  let r ← s.result
  pure (r, s.accesses, s.memory)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact zero-capacity behavior for a one-byte source and arbitrary memory. -/
theorem zero_capacity_one_byte (m : Memory) :
    observe (run 40 program (initial 131072 262144 1 0 m)) =
      some ((if m.get 131072 != 0 then 4294967295 else 0),
        [⟨false, 131072, 1⟩], m) := by
  rfl

/-- Exact zero-capacity behavior throughout the caller address region.
    The result also states that memory is unchanged and lists every access. -/
theorem zero_capacity (src dst size : Nat) (m : Memory)
    (hs : 131072 ≤ src) (he : src < 2097152) :
    observe (run 40 program (initial src dst size 0 m)) =
      some (if size = 1 then (if m.get src = 0 then 0 else 4294967295)
            else 4294967295,
        if size = 1 then [⟨false, src, 1⟩] else [], m) := by
  have hn : src ≠ 0 := by omega
  have hb : src + 1 ≤ 2097152 := by omega
  by_cases hsize : size = 1
  · subst size
    by_cases hz : m.get src = 0
    · repeat (rw [run]; simp [observe, step, initial, binop, Wasm.bool,
        signed, Memory.load, hn, hb, hz])
    · repeat (rw [run]; simp [observe, step, initial, binop, Wasm.bool,
        signed, Memory.load, hn, hb, hz])
  · repeat (rw [run]; simp [observe, step, initial, binop, Wasm.bool,
        signed, hn, hsize])

/-- Empty compressed input is rejected without any access, at every
    nonnegative i32 capacity and every caller-region source address. -/
theorem zero_source (src dst capacity : Nat) (m : Memory)
    (hs : 131072 ≤ src) (hc : capacity < 2147483648) :
    observe (run 40 program (initial src dst 0 capacity m)) =
      some (4294967295, [], m) := by
  have hn : src ≠ 0 := by omega
  by_cases hz : capacity = 0
  · subst capacity
    repeat (rw [run]; simp [observe, step, initial, binop, Wasm.bool,
      signed, hn])
  · repeat (rw [run]; simp [observe, step, initial, binop, Wasm.bool,
      signed, hn, hc, hz])

/-- The valid empty block succeeds even at zero destination capacity. -/
theorem empty_block (src dst : Nat) (m : Memory)
    (hs : 131072 ≤ src) (he : src < 2097152) (hz : m.get src = 0) :
    observe (run 40 program (initial src dst 1 0 m)) =
      some (0, [⟨false, src, 1⟩], m) := by
  rw [zero_capacity src dst 1 m hs he]
  simp [hz]

#print axioms zero_capacity
#print axioms zero_source
#print axioms empty_block

end Boundary
