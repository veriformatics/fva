import FVATest.Subjects.Lz4.Format

/-! # Blocks the reference decoder may accept (`lz4_Block_format.md`, "Safe decoding") -/

namespace Lz4

/-- Block `b` is the sequences `ss`, then a last sequence of the literals `last` alone, whose
token's unused low field is `low`; offsets are 0 … 65535 and matches 4 bytes or longer. This is
`Parses` with offset 0 allowed: `copy` then appends `out[out.length]!`, a 0, for each byte of
such a match, as the reference decoder writes. -/
def ParsesAny (b : List UInt8) (ss : List Seq) (last : List UInt8) : Prop :=
  ∃ low < 16, b = ss.flatMap Seq.bytes ++ head last low ∧
    ∀ s ∈ ss, s.off < 65536 ∧ 4 ≤ s.len

end Lz4
