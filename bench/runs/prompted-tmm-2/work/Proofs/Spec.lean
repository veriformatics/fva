import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace TMM

-- Mathematical TMM, with average ranks for ties, as in both supplied sources.
abbrev Matrix := List (List Nat)
def total (x : Matrix) (j : Nat) : Nat := (x.map (·[j]!)).sum
def pairs (x : Matrix) (j r : Nat) : List (Nat × Nat) :=
  (x.map fun row => (row[j]!, row[r]!)).filter fun p => 0 < p.1 && 0 < p.2
def ratio (no nr : Nat) (p : Nat × Nat) : ℚ := ((p.1 * nr : Nat) : ℚ) / (p.2 * no : Nat)
-- Twice the average rank. M is ordered by obs/ref; A by obs*ref.
-- The logarithm and library-size constants do not change either order.
def mRank2 (ps : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  2 * (ps.filter fun t => t.1*p.2 < p.1*t.2).length +
    (ps.filter fun t => t.1*p.2 == p.1*t.2).length + 1
def aRank2 (ps : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  2 * (ps.filter fun t => t.1*t.2 < p.1*p.2).length +
    (ps.filter fun t => t.1*t.2 == p.1*p.2).length + 1
def kept (x : Matrix) (j r : Nat) : List (Nat × Nat) := Id.run do
  let ps := pairs x j r
  let n := ps.length
  return ps.filter fun p =>
    let m := mRank2 ps p
    let a := aRank2 ps p
    2 * (n * 3 / 10 + 1) ≤ m && m ≤ 2 * (n - n * 3 / 10) &&
    2 * (n / 20 + 1) ≤ a && a ≤ 2 * (n - n / 20)
def weight (no nr : Nat) (p : Nat × Nat) : ℚ :=
  1 / (((no : ℚ) - p.1) / (no * p.1) + ((nr : ℚ) - p.2) / (nr * p.2))
def terms (x : Matrix) (j r : Nat) : List (ℚ × ℚ) :=
  (kept x j r).map fun p => (ratio (total x j) (total x r) p,
    weight (total x j) (total x r) p)
noncomputable def meanLog (ts : List (ℚ × ℚ)) : ℝ :=
  (ts.map fun p => (p.2 : ℝ) * Real.log (p.1 : ℝ)).sum / (ts.map fun p => (p.2 : ℝ)).sum
noncomputable def factor (x : Matrix) (j r : Nat) : ℝ :=
  Real.exp (meanLog (terms x j r) -
    ((List.range 7).map fun k => meanLog (terms x k r)).sum / 7)

-- R's default type-7 75th percentile; all-zero rows have no effect here
-- because the shipped matrix has none (checked separately).
def orderStatistic (xs : List Nat) (k : Nat) : Nat :=
  ((List.range (xs.foldl max 0 + 1)).find? fun n =>
    k < (xs.filter (· ≤ n)).length).getD 0
def quartile (x : Matrix) (j : Nat) : ℚ := Id.run do
  let ys := x.map (·[j]!)
  let h := (ys.length - 1) * 3
  let k := h / 4
  let a := orderStatistic ys k
  let b := orderStatistic ys (k+1)
  return (a : ℚ) + ((h % 4 : Nat) : ℚ) / 4 * ((b : ℚ) - a)
def referenceOK (x : Matrix) (r : Nat) : Prop :=
  let qs := (List.range 7).map fun j => quartile x j / total x j
  let avg := qs.sum / 7
  0 < qs[r]! ∧ ∀ j ∈ List.range 7, |qs[r]! - avg| ≤ |qs[j]! - avg|

end TMM
