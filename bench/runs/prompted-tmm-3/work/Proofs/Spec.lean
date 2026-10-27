import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Proofs.Artifact

namespace Verification
open Artifact
-- Input decoding is exact decimal arithmetic; no machine floats occur here.
def fields (sep : Nat) (bs : List Nat) : List (List Nat) := bs.splitOn sep
def lines (bs : List Nat) : List (List Nat) := (fields 10 bs).filter (· != [])
def digits (bs : List Nat) : Nat := bs.foldl (fun a c => 10 * a + (c - 48)) 0
def decimal (bs : List Nat) : ℚ :=
  let p := fields 46 bs
  (digits p[0]! : ℚ) +
    (if p.length = 2 then (digits p[1]! : ℚ) / 10 ^ p[1]!.length else 0)
def counts : List (List Nat) := (lines countsBytes).map fun s =>
  (fields 9 s).map digits
def edge : List ℚ := (lines edgeBytes).map decimal
def rna : List ℚ := (lines rnaBytes).map decimal
def lib (i : Nat) : Nat := (counts.map (·[i]!)).sum
-- R's type-7 upper quartile, followed by the documented nearest-to-mean rule.
def orderStat (c : List Nat) (k : Nat) : Nat :=
  ((List.range (c.foldl max 0 + 1)).find? fun x => k < (c.filter (· ≤ x)).length).getD 0
def uq (i : Nat) : ℚ :=
  let c := counts.map (·[i]!)
  let h := 3 * (c.length - 1)
  ((4 - h % 4) * orderStat c (h / 4) + h % 4 * orderStat c (h / 4 + 1) : Nat) / (4 : ℚ) / lib i
def uqMean : ℚ := ((List.range 7).map uq).sum / 7
def reference : Nat := (List.range 7).foldl
  (fun b i => if |uq i - uqMean| < |uq b - uqMean| then i else b) 0
-- A pair retains its multiplicity: every eligible gene contributes once.
def pairs (i : Nat) : List (Nat × Nat) :=
  ((counts.filter fun r => r[i]! > 0 && r[reference]! > 0).map
    fun r => (r[i]!, r[reference]!))
def ratio (i : Nat) (p : Nat × Nat) : ℚ :=
  (p.1 * lib reference : Nat) / (p.2 * lib i : Nat)
def weight (i : Nat) (p : Nat × Nat) : ℚ :=
  ((lib i - p.1 : Nat) / ((lib i * p.1 : Nat) : ℚ) +
   (lib reference - p.2 : Nat) / ((lib reference * p.2 : Nat) : ℚ))⁻¹
-- Twice the average rank, so tied observations need no rounding.
def rank2 {α : Type} [LinearOrder α] (xs : List α) (x : α) : Nat :=
  2 * (xs.filter (· < x)).length + (xs.filter (· = x)).length + 1
def kept (i : Nat) (aNum aDen : Nat) : List (Nat × Nat) :=
  let ps := pairs i
  let n := ps.length
  let ms := ps.map (ratio i)
  let aa := ps.map fun p => p.1 * p.2
  ps.filter fun p =>
    let m := rank2 ms (ratio i p)
    let a := rank2 aa (p.1 * p.2)
    2 * (n * 3 / 10 + 1) ≤ m && m ≤ 2 * (n - n * 3 / 10) &&
    2 * (n * aNum / aDen + 1) ≤ a && a ≤ 2 * (n - n * aNum / aDen)
noncomputable def raw (i aNum aDen : Nat) : ℝ :=
  if i = reference then 0 else
    ((kept i aNum aDen).map fun p =>
      (weight i p : ℝ) * Real.log (ratio i p : ℝ)).sum /
    (((kept i aNum aDen).map (weight i)).sum : ℚ)
noncomputable def factor (i aNum aDen : Nat) : ℝ :=
  Real.exp (raw i aNum aDen - ((List.range 7).map fun j => raw j aNum aDen).sum / 7)
noncomputable def tolerance : ℝ := 1 / 10000000000
noncomputable def Meets (artifact : List ℚ) (aNum aDen : Nat) : Prop :=
  ∀ i < 7, |((artifact[i]! : ℚ) : ℝ) - factor i aNum aDen| ≤ tolerance
-- R1 and default R2 use a_trim=.05. R2's summary also says m_trim for A;
-- the literal .30 reading is checked separately.
end Verification
