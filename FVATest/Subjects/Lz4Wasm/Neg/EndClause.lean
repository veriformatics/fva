import FVATest.Subjects.Lz4Wasm.Proof
/-! E2: End-of-block condition 3 is real (last match ≥ 12 bytes before the end). This is the
obligation `EndOk` imposes on the block's last sequence; it is false (the match covers 10), so the
proof fails — a weaker clause (e.g. `0 ≤ …`) would let it through. -/
open Lz4 Subjects.Lz4Wasm
example : 5 ≤ encLast.length ∧ 12 ≤ encSeq.len + encLast.length := by decide
