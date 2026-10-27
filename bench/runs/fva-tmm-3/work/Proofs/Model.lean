import FVA.Spec.Rel.Text
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Floor

/-! Exact-real TMM on a finite, nonnegative count matrix. Columns and gene indices
are zero based. Rank ties receive their average rank. The formula uses natural
logs; changing the base cancels against exponentiation. This model describes the
documented mathematical calculation, not floating point R or NumPy execution. -/

namespace Proofs

abbrev Matrix := List (List Nat)

def countBytes (xs : Matrix) : List UInt8 :=
  xs.flatMap fun row => List.flatten ((row.map FVA.Cert.decimal).intersperse [9]) ++ [10]

/-- A nonnegative decimal numeral, preserving the number of fractional digits. -/
abbrev Decimal := Nat × Nat

def decimalValue (d : Decimal) : ℚ := (d.1 : ℚ) / 10 ^ d.2

def decimalBytes (d : Decimal) : List UInt8 :=
  let frac := FVA.Cert.decimal (d.1 % 10 ^ d.2)
  FVA.Cert.decimal (d.1 / 10 ^ d.2) ++ [46] ++
    List.replicate (d.2 - frac.length) 48 ++ frac

def factorBytes (ds : List Decimal) : List UInt8 :=
  ds.flatMap fun d => decimalBytes d ++ [10]

def column (xs : Matrix) (j : Nat) : List Nat := xs.map (fun r => r[j]?.getD 0)

def library (xs : Matrix) (j : Nat) : Nat := (column xs j).sum

def nonzero (xs : Matrix) : Matrix := xs.filter (fun r => r.any (· > 0))

/-- Zero-based order statistic: the smallest value with more than k observations
at or below it. All input observations are natural counts. -/
def orderStatistic (ys : List Nat) (k : Nat) : Nat :=
  ((List.range (ys.foldl max 0 + 1)).find?
    (fun v => k < (ys.filter (· ≤ v)).length)).getD 0

/-- R/NumPy's default linear interpolated 75th percentile, divided by library size. -/
def quartile (xs : Matrix) (j : Nat) : ℚ :=
  let ys := column (nonzero xs) j
  let k := 3 * (ys.length - 1) / 4
  let r := 3 * (ys.length - 1) % 4
  ((4 - r : Nat) * (orderStatistic ys k) + r * (orderStatistic ys (k+1)) : Nat) /
    (4 * library xs j : ℚ)

/-- First column whose normalized upper quartile is closest to the mean. -/
def reference (xs : Matrix) : Nat :=
  let n := (xs.headD []).length
  let qs := (List.range n).map (quartile xs)
  let mean := qs.sum / (n : ℚ)
  (List.range n).foldl (fun best j =>
    if |qs[j]?.getD 0 - mean| < |qs[best]?.getD 0 - mean| then j else best) 0

def positivePairs (xs : Matrix) (j r : Nat) : List (Nat × Nat) :=
  ((column xs j).zip (column xs r)).filter (fun p => p.1 > 0 && p.2 > 0)

/-- Twice the average rank; `cmp = 0` means equality. -/
def rank2 (ps : List (Nat × Nat)) (cmp : (Nat × Nat) → (Nat × Nat) → Ordering)
    (p : Nat × Nat) : Nat :=
  2 * (ps.filter (fun q => cmp q p == .lt)).length +
    (ps.filter (fun q => cmp q p == .eq)).length + 1

/-- Ordering M is ordering obs/ref; ordering A is ordering obs*ref. -/
def cmpM (p q : Nat × Nat) : Ordering := compare (p.1 * q.2) (q.1 * p.2)
def cmpA (p q : Nat × Nat) : Ordering := compare (p.1 * p.2) (q.1 * q.2)

/-- Inclusive rank bounds, 30% of each M tail and 5% of each A tail. -/
def keptPairs (xs : Matrix) (j r : Nat) : List (Nat × Nat) :=
  let ps := positivePairs xs j r
  let n := ps.length
  ps.filter fun p =>
    2 * (3*n/10 + 1) ≤ rank2 ps cmpM p && rank2 ps cmpM p ≤ 2 * (n - 3*n/10) &&
    2 * (n/20 + 1) ≤ rank2 ps cmpA p && rank2 ps cmpA p ≤ 2 * (n - n/20)

/-- Inverse asymptotic binomial variance (default weighting). -/
def weight (no nr : Nat) (p : Nat × Nat) : ℚ :=
  1 / (((no : ℚ) - p.1) / ((no : ℚ) * p.1) +
    ((nr : ℚ) - p.2) / ((nr : ℚ) * p.2))

noncomputable def logRatio (no nr : Nat) (p : Nat × Nat) : ℝ :=
  Real.log p.1 - Real.log p.2 + Real.log nr - Real.log no

noncomputable def score (xs : Matrix) (j r : Nat) : ℝ :=
  let ps := keptPairs xs j r
  let no := library xs j
  let nr := library xs r
  (ps.map (fun p => (weight no nr p : ℝ) * logRatio no nr p)).sum /
    (ps.map (fun p => (weight no nr p : ℝ))).sum

/-- Geometrically centered TMM factor. The input has seven columns. -/
noncomputable def factor (xs : Matrix) (j : Nat) : ℝ :=
  let r := reference xs
  let ss := (List.range 7).map (fun k => score xs k r)
  Real.exp (score xs j r - ss.sum / 7)

end Proofs
