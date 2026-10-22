import FVA.Spec.Syntax

/-!
# Byte reader for the kernel-evaluated decoder

Bytes are a little-endian packed `Nat` plus an explicit length, so the kernel decodes with
GMP-backed `&&&`, `>>>` on one numeral instead of walking a list literal. All recursion is
structural on an explicit fuel bound: well-founded recursion stalls kernel evaluation.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Decoding failures, with the byte offset where they were detected. -/
inductive DecodeError where
  /-- The bytes violate the binary format. -/
  | malformed (pos : Nat) (msg : String)
  /-- The bytes use a feature outside FVA's profile (e.g. SIMD, atomics). -/
  | unsupported (pos : Nat) (msg : String)
  deriving Repr, DecidableEq

/-- Remaining input: `len` bytes packed little-endian in `val`, starting at file offset `pos`. -/
structure Reader where
  /-- Packed bytes, first byte least significant. -/
  val : Nat
  /-- Number of remaining bytes. -/
  len : Nat
  /-- File offset of the next byte. -/
  pos : Nat
  deriving Repr

/-- Decoder results: a value and the rest of the input, or an error. A notation, not an `abbrev`,
so `do` blocks see the `Except` monad directly. -/
scoped notation:max "Res " α:max => Except DecodeError (α × Reader)

/-- Fail as malformed at the reader's position. -/
@[inline] def Reader.bad {α : Type} (r : Reader) (msg : String) : Res α :=
  .error (.malformed r.pos msg)

/-- Fail as unsupported at the reader's position. -/
@[inline] def Reader.unsup {α : Type} (r : Reader) (msg : String) : Res α :=
  .error (.unsupported r.pos msg)

/-- Next byte. -/
def Reader.byte (r : Reader) : Res UInt8 :=
  if r.len = 0 then r.bad "unexpected end"
  else .ok ((r.val &&& 255).toUInt8, ⟨r.val >>> 8, r.len - 1, r.pos + 1⟩)

/-- Split off the next `k` bytes as their own reader. -/
def Reader.take (r : Reader) (k : Nat) : Res Reader :=
  if r.len < k then r.bad "unexpected end"
  else .ok (⟨r.val &&& ((1 <<< (8 * k)) - 1), k, r.pos⟩, ⟨r.val >>> (8 * k), r.len - k, r.pos + k⟩)

/-- `uN` (spec §5.2.2): at most ⌈N/7⌉ bytes, unused high bits of the last byte zero. -/
def uleb : Nat → Nat → Reader → Res Nat
  | 0, _, r => r.bad "integer representation too long"
  | fuel + 1, N, r => do
    let (b, r) ← r.byte
    let n := b.toNat
    if n < 128 then
      if n < 2 ^ N then .ok (n, r) else r.bad "integer too large"
    else if 7 < N then do
      let (m, r) ← uleb fuel (N - 7) r
      .ok (128 * m + (n - 128), r)
    else r.bad "integer representation too long"

/-- `sN` (spec §5.2.2). -/
def sleb : Nat → Nat → Reader → Res Int
  | 0, _, r => r.bad "integer representation too long"
  | fuel + 1, N, r => do
    let (b, r) ← r.byte
    let n := b.toNat
    if n < 64 then
      if n < 2 ^ (N - 1) then .ok (n, r) else r.bad "integer too large"
    else if n < 128 then
      if (2 ^ 7 : Int) - 2 ^ (N - 1) ≤ n then .ok ((n : Int) - 128, r)
      else r.bad "integer too large"
    else if 7 < N then do
      let (m, r) ← sleb fuel (N - 7) r
      .ok (128 * m + ((n : Int) - 128), r)
    else r.bad "integer representation too long"

/-- `u32`. -/
@[inline] def u32 (r : Reader) : Res Nat := uleb 5 32 r

/-- `k` raw bytes as a little-endian number. -/
def leNat (k : Nat) (r : Reader) : Res Nat := do
  let (s, r) ← r.take k
  .ok (s.val, r)

/-- `count` repetitions of a reader action (structural on `count`). -/
def many {α : Type} (p : Reader → Res α) : Nat → Reader → Res (List α)
  | 0, r => .ok ([], r)
  | count + 1, r => do
    let (a, r) ← p r
    let (as, r) ← many p count r
    .ok (a :: as, r)

/-- `vec(B)`: a `u32` count then that many elements. -/
def vec {α : Type} (p : Reader → Res α) (r : Reader) : Res (List α) := do
  let (n, r) ← u32 r
  if r.len < n then r.bad "length out of bounds" else many p n r

/-- Raw bytes as a list (structural on the count). -/
def bytesList : Nat → Reader → Res (List UInt8)
  | 0, r => .ok ([], r)
  | k + 1, r => do
    let (b, r) ← r.byte
    let (bs, r) ← bytesList k r
    .ok (b :: bs, r)

/-- Decode one UTF-8 scalar value from a byte list (spec §5.2.4, Unicode 3.9 well-formed). -/
def utf8Char : List UInt8 → Option (Char × List UInt8)
  | b₁ :: rest =>
    let c₁ := b₁.toNat
    if c₁ < 0x80 then (some (Char.ofNat c₁, rest))
    else if c₁ < 0xC2 then none
    else if c₁ < 0xE0 then
      match rest with
      | b₂ :: rest =>
        let c₂ := b₂.toNat
        if 0x80 ≤ c₂ ∧ c₂ < 0xC0 then some (Char.ofNat ((c₁ - 0xC0) * 64 + (c₂ - 0x80)), rest)
        else none
      | [] => none
    else if c₁ < 0xF0 then
      match rest with
      | b₂ :: b₃ :: rest =>
        let c₂ := b₂.toNat
        let c₃ := b₃.toNat
        let v := (c₁ - 0xE0) * 4096 + (c₂ - 0x80) * 64 + (c₃ - 0x80)
        if 0x80 ≤ c₂ ∧ c₂ < 0xC0 ∧ 0x80 ≤ c₃ ∧ c₃ < 0xC0 ∧ 0x800 ≤ v ∧ (v < 0xD800 ∨ 0xE000 ≤ v)
        then some (Char.ofNat v, rest) else none
      | _ => none
    else if c₁ < 0xF5 then
      match rest with
      | b₂ :: b₃ :: b₄ :: rest =>
        let c₂ := b₂.toNat
        let c₃ := b₃.toNat
        let c₄ := b₄.toNat
        let v := (c₁ - 0xF0) * 262144 + (c₂ - 0x80) * 4096 + (c₃ - 0x80) * 64 + (c₄ - 0x80)
        if 0x80 ≤ c₂ ∧ c₂ < 0xC0 ∧ 0x80 ≤ c₃ ∧ c₃ < 0xC0 ∧ 0x80 ≤ c₄ ∧ c₄ < 0xC0 ∧
            0x10000 ≤ v ∧ v < 0x110000
        then some (Char.ofNat v, rest) else none
      | _ => none
    else none
  | [] => none

/-- Decode a whole byte list as UTF-8 (structural on fuel ≥ byte count). -/
def utf8Chars : Nat → List UInt8 → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs@(_ :: _) => do
    let (c, rest) ← utf8Char bs
    let cs ← utf8Chars fuel rest
    some (c :: cs)

/-- `name`: `vec(byte)` that must be well-formed UTF-8. -/
def name (r : Reader) : Res String := do
  let (n, r) ← u32 r
  let start := r
  let (bs, r) ← bytesList n r
  match utf8Chars bs.length bs with
  | some cs => .ok (String.ofList cs, r)
  | none => start.bad "malformed UTF-8 encoding"

end FVA.Wasm.Decode
