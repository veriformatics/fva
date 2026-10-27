import Proofs.Input
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Verification

def edge : List ℚ := edgeData.map (fun p => (p.1 : ℚ) / 10 ^ p.2)
def rna : List ℚ := rnaData.map (fun p => (p.1 : ℚ) / 10 ^ p.2)

def column (i : Nat) : List Nat := matrix.map (fun r => r[i]!)
def library (i : Nat) : Nat := (column i).sum
-- Zero-indexed order statistic, characterized by counts, including ties.
def kth (xs : List Nat) (k : Nat) : Nat :=
  ((List.range (xs.foldl max 0 + 1)).find? (fun v => k < (xs.filter (· ≤ v)).length)).getD 0
-- R's default type-7 quantile with linear interpolation.
def uq (i : Nat) : ℚ :=
  let xs := column i
  let k := 3 * (xs.length - 1)
  ((kth xs (k / 4) : ℚ) * (4 - k % 4) + (kth xs (k / 4 + 1) : ℚ) * (k % 4)) /
    (4 * library i)
def uqMean : ℚ := ((List.range 7).map uq).sum / 7
def refIndex : Nat := (List.range 7).foldl (fun best i =>
  if |uq i - uqMean| < |uq best - uqMean| then i else best) 0

def pairs (i : Nat) : List (Nat × Nat) :=
  (matrix.map (fun row => (row[i]!, row[refIndex]!))).filter
    (fun p => 0 < p.1 && 0 < p.2)
-- Strict order of exact M and A, using monotonicity of log.
def mLT (p q : Nat × Nat) : Bool := p.1 * q.2 < q.1 * p.2
def aLT (p q : Nat × Nat) : Bool := p.1 * p.2 < q.1 * q.2
-- Twice the average rank, including ties. R and scipy use average ranks.
def rank2 (lt : (Nat × Nat) → (Nat × Nat) → Bool)
    (ps : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  2 * (ps.filter (fun q => lt q p)).length +
    (ps.filter (fun q => !lt q p && !lt p q)).length + 1
def inTrim (r n num den : Nat) : Bool :=
  2 * (n * num / den + 1) ≤ r && r ≤ 2 * (n - n * num / den)
def kept (i : Nat) : List (Nat × Nat) :=
  let ps := pairs i
  ps.filter (fun p => inTrim (rank2 mLT ps p) ps.length 3 10 &&
    inTrim (rank2 aLT ps p) ps.length 1 20)
def ratio (i : Nat) (p : Nat × Nat) : ℚ :=
  (p.1 * library refIndex : ℚ) / (p.2 * library i)
def weight (i : Nat) (p : Nat × Nat) : ℚ :=
  1 / ((1 / (p.1 : ℚ) - 1 / library i) + (1 / (p.2 : ℚ) - 1 / library refIndex))
def terms (i : Nat) : List (ℚ × ℚ) := (kept i).map (fun p => (weight i p, ratio i p))
-- Natural logs replace log2: base cancels with the final exponentiation.
noncomputable def raw (i : Nat) : ℝ :=
  ((terms i).map (fun p => (p.1 : ℝ) * Real.log (p.2 : ℝ))).sum /
    (((terms i).map Prod.fst).sum : ℚ)
noncomputable def tmm (i : Nat) : ℝ :=
  Real.exp (raw i - ((List.range 7).map raw).sum / 7)
def tolerance : ℚ := 1 / 10000000000
noncomputable def Meets (out : List ℚ) : Prop :=
  ∀ i ∈ List.range 7, |(out[i]! : ℝ) - tmm i| ≤ (tolerance : ℝ)

end Verification
