import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Proofs.Artifact

namespace Verification

-- embed.py binds these exact integers/rationals to the original ASCII bytes.
def counts : List (List Nat) := Artifact.matrix
def edge : List ℚ := Artifact.edge
def rna : List ℚ := Artifact.rna
def column (j : Nat) : List Nat := counts.map (fun r => r[j]!)
def library (j : Nat) : Nat := (column j).sum
-- R type-7 / scipy linear 75% quantile, specialized to the checked 454 rows.
def orderStat (j k : Nat) : Nat :=
  ((List.range (library j + 1)).find?
    (fun v => k < ((column j).filter (· ≤ v)).length)).getD 0
def quartile (j : Nat) : ℚ :=
  ((orderStat j 339 : ℚ) + 3 * orderStat j 340) / 4 / library j
def qmean : ℚ := ((List.range 7).map quartile).sum / 7
def reference : Nat := (List.range 7).foldl
  (fun best j => if |quartile j - qmean| < |quartile best - qmean| then j else best) 0

-- Only the first sample and reference sample are needed to refute conformance.
def pairs : List (Nat × Nat) :=
  (counts.map (fun r => (r[0]!, r[reference]!))).filter
    (fun p => 0 < p.1 && 0 < p.2)
-- Twice the average rank: 2 * number strictly below + number equal + 1.
def rank₂ (lt eq : (Nat × Nat) → (Nat × Nat) → Bool) (p : Nat × Nat) : Nat :=
  2 * (pairs.filter (fun q => lt q p)).length +
    (pairs.filter (fun q => eq q p)).length + 1
-- log and log2 are strictly increasing: compare ratios and products exactly.
def mlt (p q : Nat × Nat) : Bool := p.1 * q.2 < q.1 * p.2
def meq (p q : Nat × Nat) : Bool := p.1 * q.2 == q.1 * p.2
def alt (p q : Nat × Nat) : Bool := p.1 * p.2 < q.1 * q.2
def aeq (p q : Nat × Nat) : Bool := p.1 * p.2 == q.1 * q.2
def retained : List (Nat × Nat) :=
  (pairs.filter fun p =>
    let mr := rank₂ mlt meq p
    let ar := rank₂ alt aeq p
    2 * (pairs.length * 3 / 10 + 1) ≤ mr && mr ≤ 2 * (pairs.length - pairs.length * 3 / 10) &&
    2 * (pairs.length / 20 + 1) ≤ ar && ar ≤ 2 * (pairs.length - pairs.length / 20)).insertionSort
      (fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2))
def weight (p : Nat × Nat) : ℚ :=
  1 / (1 / (p.1 : ℚ) - 1 / (library 0 : ℚ) +
       1 / (p.2 : ℚ) - 1 / (library reference : ℚ))
def ratio (p : Nat × Nat) : ℚ :=
  (p.1 : ℚ) * library reference / ((p.2 : ℚ) * library 0)
noncomputable def logMean : ℝ :=
  (retained.map (fun p => (weight p : ℝ) * Real.log (ratio p : ℝ))).sum /
    ((retained.map weight).sum : ℚ)
noncomputable def rawFirst : ℝ := Real.exp logMean
-- Necessary relation for normalized samples 1 and 4. The common positive
-- geometric rescaling cancels; comparison of a reference to itself gives 1.
def DocumentedPair (first fourth : ℝ) : Prop :=
  ∃ scale : ℝ, 0 < scale ∧ first = rawFirst * scale ∧ fourth = scale
def FitsPair (f : List ℚ) (tolerance : ℝ) : Prop :=
  ∃ first fourth : ℝ, DocumentedPair first fourth ∧
    |first - (f[0]! : ℝ)| ≤ tolerance ∧ |fourth - (f[3]! : ℝ)| ≤ tolerance

end Verification
