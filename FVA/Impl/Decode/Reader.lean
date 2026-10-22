import FVA.Spec.Syntax

/-!
# Byte input for the kernel-evaluated decoder

The input is `n` bytes packed little-endian in the numeral `v`; the kernel reads it with
GMP-backed `Nat.land` and `Nat.shiftRight` and never builds a byte list. The kernel evaluates
lazily, one definition unfolding at a time, so cost tracks unfoldings (measured on 4 KB:
`Except` + `do` + `if` = 223 µs/byte, this shape ≈ 80 µs/byte):

* tests are `bif` on `Nat.blt`/`Nat.beq` (one GMP step); `if` on `Prop` unfolds `Decidable`
  instances, and a `match` on numerals compiles to a linear chain of `Nat.decEq` tests;
* results are the concrete `Res`, sequenced by `Res.bind`, not a monad stack;
* hot paths call `Nat.land`, `Nat.shiftRight`, `Nat.pow`, … directly: `&&&` and friends
  unfold through two instance layers before reaching the GMP-backed function;
* recursion is structural on an explicit fuel bound (well-founded recursion stalls the kernel).
-/

namespace FVA.Wasm.Decode

open FVA.Wasm

/-- Decoding failures, at a byte offset of the file. -/
inductive DecodeError where
  /-- The bytes violate the binary format. -/
  | malformed (pos : Nat) (msg : String)
  /-- The bytes use a feature outside FVA's profile (e.g. SIMD, atomics). -/
  | unsupported (pos : Nat) (msg : String)
  deriving Repr, DecidableEq

/-- A decoder step's result on an input `(v, n)`: a value and the rest of the input, or a
failure with the number of input bytes left at the failure point (`sub` rebases it onto the
enclosing input; `decode` turns it into a file offset). -/
inductive Res (α : Type) where
  /-- Success: the value and the remaining input. -/
  | ok (a : α) (v n : Nat)
  /-- Malformed input. -/
  | bad (rem : Nat) (msg : String)
  /-- Input outside the profile. -/
  | unsup (rem : Nat) (msg : String)

/-- Continue with the value and the rest of the input; failures pass through. -/
def Res.bind {α β : Type} (x : Res α) (f : α → Nat → Nat → Res β) : Res β :=
  match x with
  | .ok a v n => f a v n
  | .bad r m => .bad r m
  | .unsup r m => .unsup r m

/-- The next byte. -/
def byte (v n : Nat) : Res Nat :=
  match n with
  | 0 => .bad 0 "unexpected end"
  | n + 1 => .ok (Nat.land v 255) (Nat.shiftRight v 8) n

/-- The next `k` bytes as one little-endian number. -/
def leNat (k v n : Nat) : Res Nat :=
  bif Nat.blt n k then .bad n "unexpected end"
  else .ok (Nat.land v (Nat.pow 2 (8 * k) - 1)) (Nat.shiftRight v (8 * k)) (Nat.sub n k)

/-- Run `p` on the next `k` bytes as an input of their own, which `p` must consume entirely. -/
def sub {α : Type} (k : Nat) (p : Nat → Nat → Res α) (v n : Nat) : Res α :=
  bif Nat.blt n k then .bad n "unexpected end" else
  match p (Nat.land v (Nat.pow 2 (8 * k) - 1)) k with
  | .ok a _ 0 => .ok a (Nat.shiftRight v (8 * k)) (Nat.sub n k)
  | .ok _ _ (r + 1) => .bad (r + 1 + (n - k)) "section size mismatch"
  | .bad r m => .bad (r + (n - k)) m
  | .unsup r m => .unsup (r + (n - k)) m

/-- `uN` (spec §5.2.2) with at most `fuel` bytes: unused bits of the last byte must be zero. -/
def uleb : Nat → Nat → Nat → Nat → Res Nat
  | 0, _, _, n => .bad n "integer representation too long"
  | fuel + 1, N, v, n =>
    match n with
    | 0 => .bad 0 "unexpected end"
    | n' + 1 =>
      let b := Nat.land v 255
      bif Nat.blt b 128 then
        (bif Nat.blt b (Nat.pow 2 N) then .ok b (Nat.shiftRight v 8) n'
         else .bad n "integer too large")
      else bif Nat.blt 7 N then
        (uleb fuel (Nat.sub N 7) (Nat.shiftRight v 8) n').bind fun m v n =>
          .ok (Nat.add (Nat.mul 128 m) (Nat.sub b 128)) v n
      else .bad n "integer representation too long"

/-- `sN` (spec §5.2.2) with at most `fuel` bytes, as the value's `N`-bit two's complement. -/
def sleb : Nat → Nat → Nat → Nat → Res Nat
  | 0, _, _, n => .bad n "integer representation too long"
  | fuel + 1, N, v, n =>
    match n with
    | 0 => .bad 0 "unexpected end"
    | n' + 1 =>
      let b := Nat.land v 255
      bif Nat.blt b 64 then
        (bif Nat.blt b (Nat.pow 2 (N - 1)) then .ok b (Nat.shiftRight v 8) n'
         else .bad n "integer too large")
      else bif Nat.blt b 128 then
        (bif Nat.ble (128 - Nat.pow 2 (N - 1)) b then
          .ok (Nat.sub (Nat.add (Nat.pow 2 N) b) 128) (Nat.shiftRight v 8) n'
         else .bad n "integer too large")
      else bif Nat.blt 7 N then
        (sleb fuel (Nat.sub N 7) (Nat.shiftRight v 8) n').bind fun m v n =>
          .ok (Nat.add (Nat.mul 128 m) (Nat.sub b 128)) v n
      else .bad n "integer representation too long"

/-- `u32`. -/
def u32 (v n : Nat) : Res Nat := uleb 5 32 v n

/-- `count` repetitions of `p`. -/
def many {α : Type} (p : Nat → Nat → Res α) : Nat → Nat → Nat → Res (List α)
  | 0, v, n => .ok [] v n
  | count + 1, v, n =>
    (p v n).bind fun a v n => (many p count v n).bind fun as v n => .ok (a :: as) v n

/-- `vec(B)`: a `u32` count, then that many elements (each at least one byte). -/
def vec {α : Type} (p : Nat → Nat → Res α) (v n : Nat) : Res (List α) :=
  (u32 v n).bind fun c v n => bif Nat.blt n c then .bad n "length out of bounds" else many p c v n

/-- `0x80 ≤ b < 0xC0`: a UTF-8 continuation byte. -/
def cont (b : Nat) : Bool := Nat.ble 0x80 b && Nat.blt b 0xC0

/-- UTF-8 scalar values filling the whole input (spec §5.2.4: well-formed per Unicode 3.9). -/
def utf8 : Nat → Nat → Nat → Res (List Char)
  | 0, v, n => .ok [] v n
  | fuel + 1, v, n =>
    match n with
    | 0 => .ok [] v 0
    | n' + 1 =>
      let b₁ := v &&& 255
      let rest (c : Nat) (k : Nat) : Res (List Char) :=
        (utf8 fuel (v >>> (8 * k)) (n - k)).bind fun cs v n => .ok (Char.ofNat c :: cs) v n
      let b₂ := (v >>> 8) &&& 255
      let b₃ := (v >>> 16) &&& 255
      let b₄ := (v >>> 24) &&& 255
      bif Nat.blt b₁ 0x80 then rest b₁ 1
      else bif Nat.blt b₁ 0xC2 then .bad (n' + 1) "malformed UTF-8 encoding"
      else bif Nat.blt b₁ 0xE0 then
        (bif Nat.ble 2 n && cont b₂ then rest ((b₁ - 0xC0) * 64 + (b₂ - 0x80)) 2
         else .bad (n' + 1) "malformed UTF-8 encoding")
      else bif Nat.blt b₁ 0xF0 then
        let c := (b₁ - 0xE0) * 4096 + (b₂ - 0x80) * 64 + (b₃ - 0x80)
        bif Nat.ble 3 n && cont b₂ && cont b₃ && Nat.ble 0x800 c &&
            (Nat.blt c 0xD800 || Nat.ble 0xE000 c) then rest c 3
        else .bad (n' + 1) "malformed UTF-8 encoding"
      else bif Nat.blt b₁ 0xF5 then
        let c := (b₁ - 0xF0) * 262144 + (b₂ - 0x80) * 4096 + (b₃ - 0x80) * 64 + (b₄ - 0x80)
        bif Nat.ble 4 n && cont b₂ && cont b₃ && cont b₄ && Nat.ble 0x10000 c &&
            Nat.blt c 0x110000 then rest c 4
        else .bad (n' + 1) "malformed UTF-8 encoding"
      else .bad (n' + 1) "malformed UTF-8 encoding"

/-- `name`: `vec(byte)` that is well-formed UTF-8. -/
def name (v n : Nat) : Res String :=
  (u32 v n).bind fun k v n =>
  sub k (fun v n => (utf8 n v n).bind fun cs v n => .ok (String.ofList cs) v n) v n

end FVA.Wasm.Decode
