import FVA.Spec.Rel.Text
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Sort

/-!
The mathematical TMM model used in this verification. Arithmetic and ties are exact.
Natural logarithms replace log2: the base cancels between the weighted mean and
exponentiation. M-ranks are ranks of count ratios; A-ranks are ranks of count
products. These transformations are strictly increasing on the positive counts.
This is deliberately an ideal-arithmetic specification, not a model of R/NumPy.
-/

namespace Proofs.Model


abbrev Matrix := List (List Nat)

/-- A finite decimal, including the number of digits after the decimal point. -/
structure Decimal where
  whole : Nat
  fraction : List Nat
  deriving DecidableEq

def Decimal.value (d : Decimal) : ℚ :=
  d.whole + (d.fraction.foldl (fun a b => 10 * a + b) 0 : Nat) /
    (10 ^ d.fraction.length : ℚ)

def Decimal.text (d : Decimal) : List UInt8 :=
  FVA.Cert.decimal d.whole ++ [46] ++ d.fraction.map (fun n => (48 + n).toUInt8) ++ [10]

def factorText (fs : List Decimal) : List UInt8 := fs.flatMap Decimal.text

def matrixText (m : Matrix) : List UInt8 := m.flatMap fun row =>
  List.intercalate [9] (row.map FVA.Cert.decimal) ++ [10]

def active (m : Matrix) : Matrix := m.filter (fun row => row.any (· != 0))

def col (m : Matrix) (j : Nat) : List Nat := m.map (fun row => row[j]?.getD 0)

def lib (m : Matrix) (j : Nat) : Nat := (col m j).sum

/-- R's default type-7 upper quartile, divided by the library size. -/
def uq (m : Matrix) (j : Nat) : ℚ :=
  let xs := (col (active m) j).mergeSort (· ≤ ·)
  let h := 3 * (xs.length - 1)
  (((4 - h % 4) * xs[h / 4]?.getD 0 + (h % 4) * xs[h / 4 + 1]?.getD 0 : Nat) : ℚ) /
    (4 * lib m j)

def reference (m : Matrix) : Nat :=
  let qs := (List.range 7).map (uq m)
  let mean := qs.sum / 7
  (List.range 7).foldl (fun best j =>
    if |uq m j - mean| < |uq m best - mean| then j else best) 0

def pairs (m : Matrix) (j r : Nat) : List (Nat × Nat) :=
  ((active m).map (fun row => (row[j]?.getD 0, row[r]?.getD 0))).filter
    (fun p => 0 < p.1 && 0 < p.2)

def ratio (p : Nat × Nat) : Nat × Nat := p

def product (p : Nat × Nat) : Nat × Nat := (p.1 * p.2, 1)

/-- Twice the usual average rank, so tied ranks can be half-integral. -/
def rank2 (xs : List (Nat × Nat)) (key : Nat × Nat → Nat × Nat)
    (p : Nat × Nat) : Nat :=
  2 * (xs.filter (fun q => (key q).1 * (key p).2 < (key p).1 * (key q).2)).length +
    (xs.filter (fun q => (key q).1 * (key p).2 = (key p).1 * (key q).2)).length + 1

/-- Default double trimming: .30 in each M tail, .05 in each A tail. -/
def kept (m : Matrix) (j r : Nat) : List (Nat × Nat) :=
  let xs := pairs m j r
  let n := xs.length
  xs.filter fun p =>
    2 * (n * 3 / 10 + 1) ≤ rank2 xs ratio p &&
    rank2 xs ratio p ≤ 2 * (n - n * 3 / 10) &&
    2 * (n / 20 + 1) ≤ rank2 xs product p &&
    rank2 xs product p ≤ 2 * (n - n / 20)

/-- Inverse asymptotic binomial variance, the default precision weight. -/
def weight (l r : Nat) (p : Nat × Nat) : ℚ :=
  (((l : ℚ) - p.1) / (l * p.1) + ((r : ℚ) - p.2) / (r * p.2))⁻¹

noncomputable def logRatio (l r : Nat) (p : Nat × Nat) : ℝ :=
  Real.log p.1 - Real.log p.2 + Real.log r - Real.log l

noncomputable def rawLog (m : Matrix) (j r : Nat) : ℝ :=
  let ps := kept m j r
  let ws := ps.map (weight (lib m j) (lib m r))
  (ps.map (fun p => (weight (lib m j) (lib m r) p : ℝ) *
    logRatio (lib m j) (lib m r) p)).sum / (ws.sum : ℝ)

/-- TMM normalization factors, centered to have geometric mean one. -/
noncomputable def factor (m : Matrix) (j : Nat) : ℝ :=
  let r := reference m
  Real.exp (rawLog m j r - ((List.range 7).map (fun k => rawLog m k r)).sum / 7)

/-- Byte-exact per-output conformance to ideal TMM, at the stated absolute tolerance. -/
def Conforms (tolerance : ℚ) (input output : List UInt8) : Prop :=
  ∃ m : Matrix, ∃ fs : List Decimal,
    input = matrixText m ∧ output = factorText fs ∧
    m.length = 454 ∧ (∀ row ∈ m, row.length = 7) ∧
    fs.length = 7 ∧ (∀ d ∈ fs, ∀ n ∈ d.fraction, n < 10) ∧
    ∀ j : Fin 7, |((fs[j.val]?.getD ⟨0, []⟩).value : ℝ) - factor m j| ≤ tolerance

/-- A concrete failure of the 10-decimal claim; even a 1e-10 error bound fails. -/
def Disagree (edge rna : List UInt8) : Prop :=
  ∃ es rs : List Decimal,
    edge = factorText es ∧ rna = factorText rs ∧ es.length = 7 ∧ rs.length = 7 ∧
    (∀ d ∈ es ++ rs, ∀ n ∈ d.fraction, n < 10) ∧
    (es[0]?.getD (⟨0, []⟩ : Decimal)).value -
      (rs[0]?.getD (⟨0, []⟩ : Decimal)).value =
        (931142302732627 / 100000000000000000 : ℚ) ∧
    ∀ j : Fin 7,
      (1 / 10000000000 : ℚ) <
        |(es[j.val]?.getD ⟨0, []⟩).value - (rs[j.val]?.getD ⟨0, []⟩).value|

/-- A failure at sample 3 of a specified absolute accuracy relative to ideal TMM. -/
def FailsTight (tolerance : ℚ) (input output : List UInt8) : Prop :=
  ∃ m : Matrix, ∃ fs : List Decimal,
    input = matrixText m ∧ output = factorText fs ∧
    m.length = 454 ∧ (∀ row ∈ m, row.length = 7) ∧ fs.length = 7 ∧
    (∀ d ∈ fs, ∀ n ∈ d.fraction, n < 10) ∧
    (tolerance : ℝ) < |((fs[2]?.getD (⟨0, []⟩ : Decimal)).value : ℝ) - factor m 2|

end Proofs.Model
