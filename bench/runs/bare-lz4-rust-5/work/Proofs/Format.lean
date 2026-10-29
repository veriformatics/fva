import Proofs.Wasm

/-!
An explicit sequence-certificate interpretation of lz4_Block_format.md.
This is a specification, not a translation of the Rust decoder.
The final token's low nibble is ignored (there is no final match).
`certificate` enforces independence, byte validity, and exact input consumption;
`endConditions` separately checks the three end-of-block restrictions.
-/
namespace LZ4

structure Sequence where
  literals : List Nat
  offset : Nat := 0  -- zero denotes the final, literal-only sequence
  matchLength : Nat := 0
  finalNibble : Nat := 0
  deriving Repr

def extension (length base : Nat) : List Nat :=
  if length < base then []
  else List.replicate ((length - base) / 255) 255 ++ [(length - base) % 255]

def encode (s : Sequence) : List Nat :=
  let lo := if s.offset = 0 then s.finalNibble else min 15 (s.matchLength - 4)
  [16 * min 15 s.literals.length + lo] ++ extension s.literals.length 15 ++
    s.literals ++
    if s.offset = 0 then []
    else [s.offset % 256, s.offset / 256] ++ extension (s.matchLength - 4) 15

def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n + 1, out => matchCopy offset n (out ++ [out[out.length - offset]!])

-- Each recursive call consumes one certificate sequence; offset validity is
-- checked after emitting literals and before emitting the match.
def interpret : List Sequence → List Nat → Option (List Nat)
  | [], _ => none
  | s :: rest, previous =>
      if !(s.literals.all (· < 256)) then none else
      let out := previous ++ s.literals
      if s.offset = 0 then
        if rest.isEmpty && s.matchLength == 0 && s.finalNibble < 16 then some out else none
      else if s.offset ≤ 65535 && s.offset ≤ out.length && 4 ≤ s.matchLength then
        interpret rest (matchCopy s.offset s.matchLength out)
      else none

def certificate (input output : List Nat) (sequences : List Sequence) : Bool :=
  sequences.flatMap encode == input && interpret sequences [] == some output

def matchStarts : List Sequence → Nat → List Nat
  | [], _ => []
  | s :: rest, pos =>
      let start := pos + s.literals.length
      if s.offset = 0 then []
      else start :: matchStarts rest (start + s.matchLength)

def endConditions (output : List Nat) (sequences : List Sequence) : Bool :=
  match sequences.getLast? with
  | none => false
  | some last =>
      last.offset == 0 &&
      (5 ≤ last.literals.length || sequences.length == 1) &&
      (matchStarts sequences 0).all (fun start => start + 12 ≤ output.length)

-- General arithmetic facts useful for the full, currently open proof.  The
-- caller's region prevents the 32-bit extension-length overflow discussed in
-- the specification, even for malicious input made entirely of 255 bytes.
theorem extension_sum_bound (xs : List Nat) (h : ∀ x ∈ xs, x ≤ 255) :
    xs.sum ≤ 255 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ a ∈ xs, a ≤ 255 := fun a ha => h a (by simp [ha])
      have hi := ih ht
      simp only [List.sum_cons, List.length_cons]
      omega

theorem lengths_fit_i32 (n cap pos extra : Nat)
    (hn : n ≤ 2097152 - 131072) (hc : cap ≤ 2097152 - 131072)
    (hp : pos ≤ cap) (he : extra ≤ 255 * n) :
    extra + 19 < Wasm.word ∧ pos + extra + 19 < Wasm.word := by
  simp only [Wasm.word]
  omega

end LZ4
