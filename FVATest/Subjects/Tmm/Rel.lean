import FVA.Spec.Rel.Text
import Mathlib.Algebra.Order.Field.Basic

/-!
# TMM factor files (reviewed; contract U14 S3)

The T5 artifacts are two text files of normalization factors, one decimal number per line.
`FactorsDiffer` is RNAnorm's documented claim, factors "identical to [edgeR's] to at least 10
decimal places", turned around: it holds when the two files differ somewhere by more than
10⁻¹⁰.
-/

namespace Subjects.Tmm

open FVA.Cert

/-- A decimal digit as text: `0` … `9` = bytes 48 … 57. -/
def digit (d : Fin 10) : UInt8 := (48 + d.val).toUInt8

/-- One nonnegative decimal number on a line: the integer part `n` in decimal, a `.` (byte 46),
the fraction digits `f`, a line feed (byte 10). -/
def decLine (n : Nat) (f : List (Fin 10)) : List UInt8 := decimal n ++ 46 :: f.map digit ++ [10]

/-- A file of such numbers, one per line. -/
def decFile (xs : List (Nat × List (Fin 10))) : List UInt8 := xs.flatMap fun x => decLine x.1 x.2

/-- The value of the fraction digits `f`: `0.f₁f₂…`. -/
def fracVal : List (Fin 10) → ℚ
  | [] => 0
  | d :: ds => (d.val + fracVal ds) / 10

/-- The value of the line for `n` and `f`. -/
def decVal (x : Nat × List (Fin 10)) : ℚ := x.1 + fracVal x.2

/-- RNAnorm's parity claim fails for the factor files `e` (edgeR) and `r` (RNAnorm): both are
files of decimal numbers, and every reading of them has a line where the two values differ by
more than 10⁻¹⁰. -/
def FactorsDiffer (e r : List UInt8) : Prop :=
  (∃ xs ys, e = decFile xs ∧ r = decFile ys) ∧
    ∀ xs ys, e = decFile xs → r = decFile ys →
      ∃ p ∈ xs.zip ys, 1 / 10 ^ 10 < |decVal p.1 - decVal p.2|

end Subjects.Tmm
