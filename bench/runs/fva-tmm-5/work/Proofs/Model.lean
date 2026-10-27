import FVA.Spec.Rel.Text
import Mathlib.Data.List.Sort
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Reviewed mathematical interpretation of default TMM. Indices are zero based.
Ranks are exact average ranks. Logarithm base does not affect the selected ranks;
using natural logs in the weighted mean makes the raw factor `exp(mean)`.
Only samples 3 and 4 are needed: a common normalization divisor cancels in their ratio.
This is a model of the documented formula, not of R/NumPy floating-point execution. -/
namespace TMM

/-- Unsigned decimal TSV, one gene per line, preserving every count. -/
def matrixBytes (m : List (List Nat)) : List UInt8 :=
  m.flatMap fun row => List.intercalate [9] (row.map FVA.Cert.decimal) ++ [10]

/-- A decimal consists of its integer part, fractional digits, and their number.
The rendering includes leading fractional zeroes. -/
structure Dec where
  whole : Nat
  fraction : Nat
  places : Nat
  deriving DecidableEq, Repr, Inhabited

def Dec.value (d : Dec) : ℚ := d.whole + d.fraction / (10 : ℚ) ^ d.places

/-- The encoded fractional digits fit the declared decimal scale. -/
def Dec.Valid (d : Dec) : Prop := 0 < d.places ∧ d.fraction < 10^d.places

def factorBytes (ds : List Dec) : List UInt8 := ds.flatMap fun d =>
  FVA.Cert.decimal d.whole ++ [46] ++
  List.replicate (d.places - (FVA.Cert.decimal d.fraction).length) 48 ++
  FVA.Cert.decimal d.fraction ++ [10]

def column (m : List (List Nat)) (j : Nat) : List Nat := m.map (fun row => row[j]!)
def library (m : List (List Nat)) (j : Nat) : Nat := (column m j).sum
def nonzero (m : List (List Nat)) : List (List Nat) := m.filter (fun row => row.any (0 < ·))

/-- R type-7 / NumPy default 75th percentile: interpolate at 3(n-1)/4. -/
def upperQuartile (xs : List Nat) : ℚ :=
  let ys := xs.insertionSort (· ≤ ·)
  let h := 3 * (xs.length - 1)
  (ys[h / 4]! : ℚ) + ((h % 4 : Nat) : ℚ) / 4 * ((ys[h / 4 + 1]! : ℚ) - ys[h / 4]!)

def quartiles (m : List (List Nat)) : List ℚ :=
  (List.range 7).map fun j => upperQuartile (column (nonzero m) j) / library m j

/-- Positive quartiles bypass edgeR's near-zero fallback. The nominated reference
is strictly closest to the mean CPM upper quartile. Rescaling all quartiles by
their geometric mean, as RNAnorm does, leaves this unique choice unchanged. -/
def UniqueReference (m : List (List Nat)) (r : Nat) : Prop :=
  let qs := quartiles m
  let a := qs.sum / 7
  r < 7 ∧ (∀ q ∈ qs, (1 : ℚ) / 10^20 < q) ∧
    ∀ j < 7, j ≠ r → |qs[r]! - a| < |qs[j]! - a|

def pairs (m : List (List Nat)) (j r : Nat) : List (Nat × Nat) :=
  ((column m j).zip (column m r)).filter fun p => 0 < p.1 && 0 < p.2

/-- Twice the average rank: ranks start at one; ties share their average. -/
def rank2 (xs : List ℚ) (x : ℚ) : Nat :=
  2 * (xs.filter (· < x)).length + (xs.filter (· = x)).length + 1

def retained (m : List (List Nat)) (j r : Nat) : List (Nat × Nat) :=
  let ps := pairs m j r
  let ms := ps.map fun p => (p.1 : ℚ) / p.2
  let aas := ps.map fun p => (p.1 * p.2 : Nat) / (1 : ℚ)
  let n := ps.length
  ps.filter fun p =>
    let rm := rank2 ms ((p.1 : ℚ) / p.2)
    let ra := rank2 aas ((p.1 * p.2 : Nat) / (1 : ℚ))
    2 * (n * 3 / 10 + 1) ≤ rm && rm ≤ 2 * (n - n * 3 / 10) &&
    2 * (n / 20 + 1) ≤ ra && ra ≤ 2 * (n - n / 20)

/-- Inverse delta-method binomial variance. -/
def weight (nO nR : Nat) (p : Nat × Nat) : ℚ :=
  1 / ((1 / (p.1 : ℚ) - 1 / nO) + (1 / (p.2 : ℚ) - 1 / nR))

def expressionRatio (nO nR : Nat) (p : Nat × Nat) : ℚ :=
  (p.1 : ℚ) * nR / ((p.2 : ℚ) * nO)

/-- Natural-log weighted mean after default 30% M and 5% A trimming.
Sorting M is sorting count ratios; sorting A is sorting count products.
For libraries at most 2000 and positive counts the default A cutoff -10^10
removes nothing. Nonpositive pairs are excluded before ranking. -/
noncomputable def meanLog (m : List (List Nat)) (j r : Nat) : ℝ :=
  let ps := retained m j r
  let nO := library m j
  let nR := library m r
  (ps.map fun p => (weight nO nR p : ℝ) * Real.log (expressionRatio nO nR p)).sum /
    ((ps.map (weight nO nR)).sum : ℚ)

/-- R1/R2 counterexample at absolute tolerance 10^-10. On this input the unique
reference is sample 4. No positive common normalization divisor can make BOTH
sample 3's exp(weighted mean) and sample 4's unit raw factor agree with the
output. Thus at least one of these two samples violates the tolerance. -/
def RejectsDefaultTMM (i o : List UInt8) : Prop :=
  ∃ m ds, i = matrixBytes m ∧ o = factorBytes ds ∧
    m.length = 454 ∧ (∀ row ∈ m, row.length = 7) ∧ ds.length = 7 ∧
    (∀ d ∈ ds, d.Valid) ∧
    (∀ j < 7, 0 < library m j ∧ library m j ≤ 2000) ∧
    UniqueReference m 3 ∧
    ∀ g : ℝ, 0 < g →
      ¬ (|Real.exp (meanLog m 2 3) / g - (ds[2]!.value : ℝ)| ≤ 1/10^10 ∧
         |1 / g - (ds[3]!.value : ℝ)| ≤ 1/10^10)

/-- R3 counterexample: the first factors in the two byte-exact output files
are more than 10^-10 apart (absolute error). -/
def Disagree (i o : List UInt8) : Prop :=
  ∃ ds es, i = factorBytes ds ∧ o = factorBytes es ∧
    ds.length = 7 ∧ es.length = 7 ∧
    (∀ d ∈ ds, d.Valid) ∧ (∀ d ∈ es, d.Valid) ∧
    (1 : ℚ)/10^10 < |ds[0]!.value - es[0]!.value|

end TMM
