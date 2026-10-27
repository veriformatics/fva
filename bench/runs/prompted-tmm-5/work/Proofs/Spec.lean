import Proofs.Artifact
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Verification
-- All sample indices are zero based.
def col (j : Nat) : List Nat := Artifact.counts.map (fun r => r.getD j 0)
def lib (j : Nat) : ℚ := ((col j).sum : Nat)
def quartiles : List Nat := [4,2,2,3,5,3,3]
def uq (j : Nat) : ℚ := (quartiles.getD j 0 : ℚ) / lib j
def uqMean : ℚ := ((List.range 7).map uq).sum / 7
def pairs : List (Nat × Nat) :=
  Artifact.counts.map (fun r => (r.getD 2 0, r.getD 3 0)) |>.filter
    (fun p => p.1 > 0 && p.2 > 0)
-- Positive counts make M ordering equal to ordering obs/ref, and A ordering
-- equal to ordering obs*ref. Integer cross products preserve exact ties.
def rankM (p : Nat × Nat) : Nat :=
  2 * (pairs.filter (fun q => q.1 * p.2 < p.1 * q.2)).length +
    (pairs.filter (fun q => q.1 * p.2 == p.1 * q.2)).length + 1
def rankA (p : Nat × Nat) : Nat :=
  2 * (pairs.filter (fun q => q.1 * q.2 < p.1 * p.2)).length +
    (pairs.filter (fun q => q.1 * q.2 == p.1 * p.2)).length + 1
def retained (aNumer aDenom : Nat) : List (Nat × Nat) :=
  let n := pairs.length
  let loM := n * 3 / 10 + 1
  let loA := n * aNumer / aDenom + 1
  pairs.filter (fun p =>
    2 * loM ≤ rankM p && rankM p ≤ 2 * (n + 1 - loM) &&
    2 * loA ≤ rankA p && rankA p ≤ 2 * (n + 1 - loA))
def ratio (p : Nat × Nat) : ℚ := (p.1 : ℚ) * lib 3 / (p.2 * lib 2)
def abundanceRatio (p : Nat × Nat) : ℚ :=
  (p.1 : ℚ) * p.2 / (lib 2 * lib 3)
def weight (p : Nat × Nat) : ℚ :=
  1 / (1 / (p.1 : ℚ) - 1 / lib 2 + 1 / (p.2 : ℚ) - 1 / lib 3)
noncomputable def logMean (ps : List (Nat × Nat)) : ℝ :=
  (ps.map (fun p => (weight p : ℝ) * Real.log (ratio p))).sum /
    ((ps.map weight).sum : ℚ)
-- A necessary condition on just samples 3 and 4, even allowing any common scale.
noncomputable def Compatible (values : List ℚ) (ps : List (Nat × Nat)) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    |c - (values.getD 3 0 : ℝ)| ≤ 1 / 10^10 ∧
    |c * Real.exp (logMean ps) - (values.getD 2 0 : ℝ)| ≤ 1 / 10^10
-- R3 is weaker here than equality after rounding to ten decimal places.
def Agree10 : Prop := ∀ j ∈ List.range 7,
  |Artifact.edge.getD j 0 - Artifact.rna.getD j 0| ≤ (1 / 10^10 : ℚ)
end Verification
