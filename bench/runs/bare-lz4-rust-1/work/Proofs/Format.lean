import Mathlib

/- Independent constructive specification of LZ4 block encodings. A Block
   supplies the sequence boundaries, offsets and match lengths. Its encoding is
   compared with the actual input, so a certificate is also a parsing witness.
   Lists contain natural-number bytes; byte validity is checked explicitly. -/
namespace LZ4

structure Sequence where
  literals : List Nat
  offset : Nat
  matchLength : Nat
  deriving Repr, DecidableEq

structure Block where
  sequences : List Sequence := []
  lastLiterals : List Nat := []
  lastNibble : Nat := 0
  deriving Repr, DecidableEq

def extension (n : Nat) : List Nat :=
  List.replicate (n/255) 255 ++ [n%255]

def literalExtension (n : Nat) : List Nat :=
  if n < 15 then [] else extension (n-15)

def Sequence.encode (s : Sequence) : List Nat :=
  [16 * min s.literals.length 15 + min (s.matchLength-4) 15] ++
  literalExtension s.literals.length ++ s.literals ++
  [s.offset%256, s.offset/256] ++
  (if s.matchLength < 19 then [] else extension (s.matchLength-19))

def Block.encode (b : Block) : List Nat :=
  b.sequences.flatMap Sequence.encode ++
  [16 * min b.lastLiterals.length 15 + b.lastNibble] ++
  literalExtension b.lastLiterals.length ++ b.lastLiterals

/-- Sequential copy: a later byte in the match can refer to an earlier byte
    produced by this same match, as required by the overlap rule. -/
def copyMatch (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n+1, out => copyMatch offset n (out ++ [out[out.length-offset]!])

def Sequence.decode (s : Sequence) (out : List Nat) : List Nat :=
  copyMatch s.offset s.matchLength (out ++ s.literals)

def Block.decode (b : Block) : List Nat :=
  b.sequences.foldl (fun out s => s.decode out) [] ++ b.lastLiterals

def bytes (xs : List Nat) : Bool := xs.all (· < 256)

def sequencesOK : List Sequence → Nat → Bool
  | [], _ => true
  | s :: ss, pos =>
    bytes s.literals && 1 ≤ s.offset && s.offset ≤ 65535 &&
    s.offset ≤ pos+s.literals.length && 4 ≤ s.matchLength &&
    sequencesOK ss (pos+s.literals.length+s.matchLength)

/-- R3's format conditions, without the optional end-of-block restrictions. -/
def Block.relaxed (b : Block) : Bool :=
  b.lastNibble < 16 && bytes b.lastLiterals && sequencesOK b.sequences 0

def matchEndsOK : List Sequence → Nat → Nat → Bool
  | [], _, _ => true
  | s :: ss, pos, total =>
    pos+s.literals.length+12 ≤ total &&
    matchEndsOK ss (pos+s.literals.length+s.matchLength) total

/-- The three end conditions: a literal-only last sequence (by construction),
    at least five final literals when any match occurs, and every match starts
    at least twelve decoded bytes before the end. No-match blocks may be short. -/
def Block.valid (b : Block) : Bool :=
  b.relaxed && (b.sequences.isEmpty || 5 ≤ b.lastLiterals.length) &&
  matchEndsOK b.sequences 0 b.decode.length

theorem copyMatch_length (off n : Nat) (out : List Nat) :
    (copyMatch off n out).length = out.length+n := by
  induction n generalizing out with
  | zero => simp [copyMatch]
  | succ n ih => simp [copyMatch, ih]; omega

theorem Sequence.decode_length (s : Sequence) (out : List Nat) :
    (s.decode out).length = out.length+s.literals.length+s.matchLength := by
  simp [Sequence.decode, copyMatch_length]

theorem valid_implies_relaxed (b : Block) (h : b.valid = true) :
    b.relaxed = true := by
  simp only [Block.valid, Bool.and_eq_true] at h
  exact h.1.1

theorem sequencesOK_head (s : Sequence) (ss : List Sequence) (pos : Nat)
    (h : sequencesOK (s::ss) pos = true) :
    1 ≤ s.offset ∧ s.offset ≤ 65535 ∧ s.offset ≤ pos+s.literals.length ∧
    4 ≤ s.matchLength := by
  simp only [sequencesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

end LZ4
