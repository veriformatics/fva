import FVATest.Subjects.Lz4C.Numeric
import FVATest.Subjects.Lz4.Format

/-!
# `LZ4_decompress_safe`'s decisions as a Lean function (proof support; outside the review surface)

The compiled decoder (func 2) read sequence by sequence: positions `i` in the input `inp`
(`n = inp.length` bytes at `src`), output `out` (the bytes decoded so far at `dst`, room `cap`).
Every comparison is the decoder's own, rewritten additively (`ip < iend − 16` ↦ `i + 16 < n`):
both buffers lie at addresses ≥ 131072 and below 2^21, so no pointer comparison wraps. The
shortcut path (literal length < 15, room for 16 + 18 bytes) and the general path differ in what
they accept — a match that fills the output to the last byte passes the shortcut but not the
general path's `cpy > oend − 5` test — so both are kept. Paths that differ only in how they copy
(the offset < 8 tables, the near-end byte loop, the wildcopies) produce the same output prefix
and are one case here. The pointer-overflow tests (`length > ~op`) never fire at these sizes and
are left out; the simulation shows they pass.
-/

namespace Subjects.Lz4C.Model

/-- The byte at position `i` (0 past the end). -/
def at! (inp : List UInt8) (i : Nat) : Nat := (inp[i]?.getD 0).toNat

/-- `read_variable_length` from position `q` onto `acc`: each byte's successor position must be
at most `n − L` (`L` = 15 for a literal length, 4 for a match length), the sum stays below 2^31,
reading continues while the byte is 255; the sum and the position after the last byte. -/
def ext (inp : List UInt8) (L : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, q, acc =>
    if q + 1 + L ≤ inp.length then
      if acc + at! inp q < 2 ^ 31 then
        if at! inp q = 255 then ext inp L fuel (q + 1) (acc + at! inp q)
        else some (acc + at! inp q, q + 1)
      else none
    else none

/-- What one sequence of the main loop does. -/
inductive Out where
  /-- The next sequence starts at `i` with output `out`. -/
  | cont (i : Nat) (out : List UInt8)
  /-- The block ended (the last literals): the decoded content. -/
  | done (out : List UInt8)
  /-- An error return. -/
  | err

/-- The little-endian offset at position `i`. -/
def off16 (inp : List UInt8) (i : Nat) : Nat := at! inp i + 256 * at! inp (i + 1)

/-- `_copy_match`: the match length field `ml0` (extension bytes from `i`), the output `out`
(the literals appended), the offset. -/
def copyMatch (inp : List UInt8) (cap i : Nat) (out : List UInt8) (off ml0 : Nat) : Out :=
  match (if ml0 = 15 then (ext inp 4 inp.length i 0).map fun (a, q) => (15 + a, q)
    else some (ml0, i)) with
  | none => .err
  | some (m, i') =>
    if out.length < off then .err
    else if cap < out.length + (m + 4) + 5 then .err
    else match Lz4.copy out off (m + 4) with
      | some out' => .cont i' out'
      | none => .err

/-- The literals of length `len` at position `i` (after the token and its extension bytes),
then the match: the general path. -/
def literal (inp : List UInt8) (cap i : Nat) (out : List UInt8) (len ml0 : Nat) : Out :=
  if cap < out.length + len + 12 ∨ inp.length < i + len + 8 then
    if i + len = inp.length ∧ out.length + len ≤ cap then .done (out ++ (inp.drop i).take len)
    else .err
  else
    copyMatch inp cap (i + len + 2) (out ++ (inp.drop i).take len) (off16 inp (i + len)) ml0

/-- One sequence from the token at position `i`. -/
def step (inp : List UInt8) (cap i : Nat) (out : List UInt8) : Out :=
  let t := at! inp i
  let ll := t / 16
  let ml0 := t % 16
  if ll = 15 then
    match ext inp 15 inp.length (i + 1) 0 with
    | none => .err
    | some (a, q) => literal inp cap q out (15 + a) ml0
  else if i + 1 + 16 < inp.length ∧ out.length + 32 ≤ cap then
    let lits := (inp.drop (i + 1)).take ll
    let off := off16 inp (i + 1 + ll)
    if ml0 ≠ 15 ∧ 8 ≤ off then
      if off ≤ out.length + ll then
        match Lz4.copy (out ++ lits) off (ml0 + 4) with
        | some out' => .cont (i + 1 + ll + 2) out'
        | none => .err
      else .err
    else copyMatch inp cap (i + 1 + ll + 2) (out ++ lits) off ml0
  else literal inp cap (i + 1) out ll ml0

/-- The main loop, one fuel unit per sequence. -/
def loop (inp : List UInt8) (cap : Nat) : Nat → Nat → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | fuel + 1, i, out => match step inp cap i out with
    | .cont i' out' => loop inp cap fuel i' out'
    | .done out' => some out'
    | .err => none

/-- `LZ4_decompress_safe(src, dst, inp.length, cap)`: the decoded content, or `none` for a
negative return. With no room, only the one-byte block `0` decodes (to nothing). -/
def decode (inp : List UInt8) (cap : Nat) : Option (List UInt8) :=
  if cap = 0 then (if inp = [0] then some [] else none)
  else if inp = [] then none
  else loop inp cap inp.length 0 []

end Subjects.Lz4C.Model
