/-!
# The LZ4 block format (`lz4_Block_format.md`, last revised 2022-07-31)

A block is a list of sequences. A sequence is a token byte (high 4 bits: the literal length, low
4 bits: the match length minus 4; a field of 15 continues in extension bytes), the literal
length's extension bytes, the literals, a 2-byte little-endian offset and the match length's
extension bytes; the last sequence stops after its literals. Decoding appends each sequence's
literals, then copies its match from `offset` bytes back in the output produced so far.
-/

namespace Lz4

/-- A sequence with a match: literals, then `len` bytes copied from `off` bytes back. -/
structure Seq where
  lits : List UInt8
  off : Nat
  len : Nat

/-- A length's extension bytes after its 4-bit token field: none below 15; from 15 on, the
remainder `n - 15` as bytes of 255 (each meaning "another byte follows"), then one byte below
255. -/
def ext (n : Nat) : List UInt8 :=
  if n < 15 then [] else List.replicate ((n - 15) / 255) 255 ++ [UInt8.ofNat ((n - 15) % 255)]

/-- A token with literal field `min lits.length 15` and low field `low`, the literal length's
extension bytes, the literals. -/
def head (lits : List UInt8) (low : Nat) : List UInt8 :=
  UInt8.ofNat (16 * min lits.length 15 + low) :: ext lits.length ++ lits

/-- The bytes of a sequence with a match. -/
def Seq.bytes (s : Seq) : List UInt8 :=
  head s.lits (min (s.len - 4) 15) ++ [UInt8.ofNat s.off, UInt8.ofNat (s.off / 256)] ++
    ext (s.len - 4)

/-- Block `b` is the sequences `ss`, then a last sequence of the literals `last` alone (end
condition 1), whose token's unused low field is `low`; offsets are 1 … 65535 and matches 4 bytes
or longer. -/
def Parses (b : List UInt8) (ss : List Seq) (last : List UInt8) : Prop :=
  ∃ low < 16, b = ss.flatMap Seq.bytes ++ head last low ∧
    ∀ s ∈ ss, 0 < s.off ∧ s.off < 65536 ∧ 4 ≤ s.len

/-- `out` followed by `n` bytes, each copied from `off` bytes back (a match longer than its offset
repeats bytes it has just written); `none` when `off` reaches before the start of `out`. -/
def copy (out : List UInt8) (off : Nat) : Nat → Option (List UInt8)
  | 0 => some out
  | n + 1 => if off ≤ out.length then copy (out ++ [out[out.length - off]!]) off n else none

/-- The output after decoding `ss` from output `out`: each sequence's literals, then its match. -/
def decode : List Seq → List UInt8 → Option (List UInt8)
  | [], out => some out
  | s :: ss, out => (copy (out ++ s.lits) s.off s.len).bind (decode ss)

/-- End conditions 2 and 3, when the block has a match: the last 5 bytes are literals, and the
last match starts at least 12 bytes before the end (its length and the last literals together
cover 12 bytes or more). -/
def EndOk (ss : List Seq) (last : List UInt8) : Prop :=
  ∀ s ∈ ss.getLast?, 5 ≤ last.length ∧ 12 ≤ s.len + last.length

/-- `b` is a valid LZ4 block whose content is `c`. -/
def Valid (b c : List UInt8) : Prop :=
  ∃ ss last, Parses b ss last ∧ (decode ss []).map (· ++ last) = some c ∧ EndOk ss last

end Lz4
