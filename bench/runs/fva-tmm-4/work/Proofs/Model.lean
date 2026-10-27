import FVA.Spec.Rel.Text
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.List.Sort

/-! Reviewed mathematical interpretation of the documented default TMM procedure.
Arithmetic is exact; ranks of ties are averaged. This does not model IEEE rounding.+-/
namespace Proofs.Model

def digits (bs : List UInt8) : Nat :=
  bs.foldl (fun n b => 10 * n + (b.toNat - 48)) 0

def lines (bs : List UInt8) : List (List UInt8) :=
  (bs.splitOn 10).filter (· != [])

def matrix (bs : List UInt8) : List (List Nat) :=
  (lines bs).map fun row => (row.splitOn 9).map digits

def decimal (bs : List UInt8) : ℚ :=
  let parts := bs.splitOn 46
  (digits (parts[0]?.getD []) : ℚ) +
    (digits (parts[1]?.getD []) : ℚ) / 10 ^ (parts[1]?.getD []).length

def factors (bs : List UInt8) : List ℚ := (lines bs).map decimal

def columns (m : List (List Nat)) : List (List Nat) :=
  (List.range 7).map fun j => m.map fun row => row[j]?.getD 0

/-- Zero-based order statistic, specified by counts strictly below and at most
the candidate. Repeated candidates have the same value. -/
def orderStat (xs : List Nat) (k : Nat) : Nat :=
  (xs.filter fun x => (xs.filter (· < x)).length ≤ k &&
    k < (xs.filter (· ≤ x)).length)[0]?.getD 0

/-- Type-7 upper quartile: index 3(n-1)/4, with linear interpolation. -/
def uq (xs : List Nat) : ℚ :=
  let k := 3 * (xs.length - 1)
  ((4 - k % 4 : Nat) : ℚ) / 4 * (orderStat xs (k / 4) : ℚ) +
    ((k % 4 : Nat) : ℚ) / 4 * (orderStat xs (k / 4 + 1) : ℚ)

/-- Reference is the first column with minimum distance of UQ/library-size
from its mean. The zero-quartile fallback is unnecessary for this input. -/
def reference (cs : List (List Nat)) : Nat :=
  let qs := cs.map fun c => uq c / (c.sum : ℚ)
  let avg := qs.sum / (qs.length : ℚ)
  let ds := qs.map fun q => |q - avg|
  ((List.range cs.length).insertionSort
    (fun i j => ds[i]?.getD 0 ≤ ds[j]?.getD 0))[0]?.getD 0

/-- Twice the average, one-based rank, including ties. -/
def rank2 (xs : List ℚ) (x : ℚ) : Nat :=
  2 * (xs.filter (· < x)).length + (xs.filter (· == x)).length + 1

/-- Entries are (positive normalized count ratio, inverse binomial variance).
Ordering M by ratio and A by count product is equivalent to ordering their
real logarithms. Zero pairs are omitted. Both tails are trimmed by average rank.
-/
def entries (obs ref : List Nat) : List (ℚ × ℚ) :=
  let no : ℚ := obs.sum
  let nr : ℚ := ref.sum
  let pairs := (obs.zip ref).filter fun p => p.1 > 0 && p.2 > 0
  let ms := pairs.map fun p => (p.1 : ℚ) * nr / ((p.2 : ℚ) * no)
  let as := pairs.map fun p => ((p.1 * p.2 : Nat) : ℚ)
  let n := pairs.length
  let kept := pairs.filter fun p =>
    let rm := rank2 ms ((p.1 : ℚ) * nr / ((p.2 : ℚ) * no))
    let ra := rank2 as ((p.1 * p.2 : Nat) : ℚ)
    2 * (n * 3 / 10 + 1) ≤ rm && rm ≤ 2 * (n - n * 3 / 10) &&
    2 * (n / 20 + 1) ≤ ra && ra ≤ 2 * (n - n / 20)
  kept.map fun p =>
    ((p.1 : ℚ) * nr / ((p.2 : ℚ) * no),
      (1 / (p.1 : ℚ) + 1 / (p.2 : ℚ) - 1 / no - 1 / nr)⁻¹)

def samples (bs : List UInt8) : List (List (ℚ × ℚ)) :=
  let m := (matrix bs).filter fun r => r.any (· > 0)
  let cs := columns m
  let ref := cs[reference cs]?.getD []
  cs.map fun c => entries c ref

noncomputable def score (es : List (ℚ × ℚ)) : ℝ :=
  (es.map fun p => (p.2 : ℝ) * Real.log (p.1 : ℝ)).sum /
    ((es.map Prod.snd).sum : ℚ)

noncomputable def tmm (bs : List UInt8) : List ℝ :=
  let ss := (samples bs).map score
  ss.map fun x => Real.exp (x - ss.sum / (ss.length : ℝ))

/-- Every sample is within absolute error `eps` of real-arithmetic default TMM. -/
def Accurate (eps : ℚ) (input output : List UInt8) : Prop :=
  (factors output).length = 7 ∧ (tmm input).length = 7 ∧
  List.Forall₂ (fun (y : ℚ) (x : ℝ) => |(y : ℝ) - x| ≤ (eps : ℝ)) (factors output) (tmm input)

/-- Agreement within a stated absolute tolerance for every corresponding factor. -/
def Agree (eps : ℚ) (a b : List UInt8) : Prop :=
  List.Forall₂ (fun x y => |x - y| ≤ eps) (factors a) (factors b)

end Proofs.Model
