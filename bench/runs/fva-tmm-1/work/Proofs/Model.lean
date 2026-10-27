import FVA.Spec.Rel.Text
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order

/-! Exact-real default TMM, with average ranks for ties. Column indices are zero based.
Natural logs replace log2: the base cancels in the weighted mean/exponentiation.
Ranking count ratios and count products is equivalent to ranking M and A respectively.
This is a mathematical model, not an IEEE-754 model of R or NumPy. -/
noncomputable section
namespace Proofs

open FVA.Cert

/-- An exact nonnegative decimal: mantissa and number of fractional places. -/
abbrev Decimal := Nat × Nat

def decimalValue (d : Decimal) : ℚ := (d.1 : ℚ) / 10 ^ d.2

def decimalText (d : Decimal) : List UInt8 :=
  decimal (d.1 / 10 ^ d.2) ++ [46] ++
  List.replicate (d.2 - (decimal (d.1 % 10 ^ d.2)).length) 48 ++
  decimal (d.1 % 10 ^ d.2) ++ [10]

def factorText (ds : List Decimal) : List UInt8 := ds.flatMap decimalText

def matrixText (xs : List (List Nat)) : List UInt8 :=
  xs.flatMap fun row => List.intercalate [9] (row.map decimal) ++ [10]

def nonzeroRows (xs : List (List Nat)) : List (List Nat) :=
  xs.filter fun row => row.any (fun x => x != 0)

def column (xs : List (List Nat)) (j : Nat) : List Nat := xs.map (fun row => row[j]!)
def library (xs : List (List Nat)) (j : Nat) : Nat := (column xs j).sum

/-- R type-7 / linearly interpolated 75th percentile, divided by library size. -/
def quartile (xs : List (List Nat)) (j : Nat) : ℚ :=
  let v := (column (nonzeroRows xs) j).mergeSort (· ≤ ·)
  let k := 3 * (v.length - 1)
  (((4 - k % 4 : Nat) : ℚ) * v[k / 4]! + (k % 4 : Nat) * v[k / 4 + 1]!) /
    4 / library xs j

/-- The reference has the least absolute distance to the mean upper quartile.
The concrete data below have a unique minimizer and positive quartiles, so the
edgeR zero-quartile fallback is inapplicable. -/
def referenceOK (xs : List (List Nat)) (r : Nat) : Prop :=
  let qs := (List.range 7).map (quartile xs)
  let avg := qs.sum / 7
  r < 7 ∧ (∀ q ∈ qs, 0 < q) ∧
    ∀ j ∈ List.range 7, j ≠ r → |quartile xs r - avg| < |quartile xs j - avg|

/-- Positive pairs; genes zero in either sample are excluded. -/
def pairs (xs : List (List Nat)) (j r : Nat) : List (Nat × Nat) :=
  ((nonzeroRows xs).map fun row => (row[j]!, row[r]!)).filter fun p => p.1 != 0 && p.2 != 0

/-- Twice the average (one-based) rank of x, including every member of a tie. -/
def rank2 (vs : List ℚ) (x : ℚ) : Nat :=
  2 * (vs.filter (· < x)).length + (vs.filter (· = x)).length + 1

def rankKeep (vs : List ℚ) (x : ℚ) (num den : Nat) : Bool :=
  let lo := vs.length * num / den + 1
  let hi := vs.length + 1 - lo
  decide (2 * lo ≤ rank2 vs x ∧ rank2 vs x ≤ 2 * hi)

/-- Remove 30% at each M tail, 5% at each A tail; ties use average ranks. -/
def selected (xs : List (List Nat)) (j r : Nat) : List (Nat × Nat) :=
  let ps := pairs xs j r
  let ms := ps.map (fun p => (p.1 : ℚ) / p.2)
  let aa := ps.map (fun p => ((p.1 * p.2 : Nat) : ℚ))
  ps.filter fun p => rankKeep ms ((p.1 : ℚ) / p.2) 3 10 &&
    rankKeep aa (p.1 * p.2 : Nat) 1 20

/-- Inverse asymptotic binomial variance, the default precision weight. -/
def weight (l lr : Nat) (p : Nat × Nat) : ℚ :=
  1 / ((1 / (p.1 : ℚ) - 1 / l) + (1 / (p.2 : ℚ) - 1 / lr))

/-- Coefficients of natural logarithms for the trimmed, weighted log factor.
The final two terms correct for library sizes. -/
def rawCoeffs (xs : List (List Nat)) (j r : Nat) : List (ℚ × Nat) :=
  let ps := selected xs j r
  let ws := (ps.map (weight (library xs j) (library xs r))).sum
  ps.flatMap (fun p =>
    let c := weight (library xs j) (library xs r) p / ws
    [(c, p.1), (-c, p.2)]) ++ [(1, library xs r), (-1, library xs j)]

def evalLogs (cs : List (ℚ × Nat)) : ℝ :=
  (cs.map fun p => (p.1 : ℝ) * Real.log p.2).sum

def rawLog (xs : List (List Nat)) (j r : Nat) : ℝ := evalLogs (rawCoeffs xs j r)

/-- Geometric-mean rescaling: the seven normalization factors multiply to one. -/
def factorLog (xs : List (List Nat)) (j r : Nat) : ℝ :=
  rawLog xs j r - ((List.range 7).map (fun k => rawLog xs k r)).sum / 7

def tmm (xs : List (List Nat)) (j r : Nat) : ℝ := Real.exp (factorLog xs j r)

/-- Domain and reference conditions for this particular matrix. -/
def matrixOK (xs : List (List Nat)) : Prop :=
  xs.length = 454 ∧ (∀ row ∈ xs, row.length = 7 ∧ ∀ x ∈ row, x ≤ 42) ∧
  (nonzeroRows xs).length = 454 ∧ referenceOK xs 3 ∧
  ∀ j ∈ List.range 7,
    0 < library xs j ∧ (selected xs j 3).length > 0 ∧
    ∀ p ∈ selected xs j 3, 0 < weight (library xs j) (library xs 3) p

end Proofs
