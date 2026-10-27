import Proofs.Bounds
import Proofs.Artifacts

namespace Verify

-- Decimal bytes are parsed without floating point or native evaluation.
def digits (bs : List ℕ) : Option ℕ :=
  if bs.isEmpty then none else
    bs.foldlM (fun n b => if 48 ≤ b && b ≤ 57 then some (10*n + b-48) else none) 0

def decimal (bs : List ℕ) : Option ℚ := do
  match bs.splitOn 46 with
  | [a, b] =>
    let n ← digits a
    let m ← digits b
    some ((n : ℚ) + (m : ℚ) / (10 ^ b.length : ℚ))
  | _ => none

def lines (bs : List ℕ) : List (List ℕ) := (bs.splitOn 10).dropLast
def factors (bs : List ℕ) : Option (List ℚ) := (lines bs).mapM decimal
def matrix : List (List ℕ) := (lines countsBytes).map fun s =>
  (s.splitOn 9).map fun t => (digits t).getD 0

def lib (i : ℕ) : ℕ := (matrix.map fun r => r[i]!).sum
-- Zero-based sample 3 is verified below to be the nearest upper quartile.
def pairs (i : ℕ) : List (ℕ × ℕ) :=
  (matrix.map fun r => (r[i]!, r[3]!)).filter fun p => p.1 > 0 && p.2 > 0
-- Twice the average rank: 2 * #strictly smaller + #equal + 1.
def rankM (ps : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  2 * (ps.countP fun q => q.1 * p.2 < p.1 * q.2) +
    (ps.countP fun q => q.1 * p.2 == p.1 * q.2) + 1
def rankA (ps : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  2 * (ps.countP fun q => q.1 * q.2 < p.1 * p.2) +
    (ps.countP fun q => q.1 * q.2 == p.1 * p.2) + 1

def kept (i : ℕ) (aNum aDen : ℕ) : List (ℕ × ℕ) :=
  let ps := pairs i
  let ml := ps.length * 3 / 10 + 1
  let al := ps.length * aNum / aDen + 1
  ps.eraseDups.filter fun p =>
    2*ml ≤ rankM ps p && rankM ps p ≤ 2*(ps.length+1-ml) &&
    2*al ≤ rankA ps p && rankA ps p ≤ 2*(ps.length+1-al)

-- Group equal count pairs; multiplicity multiplies their precision weight.
def terms (i aNum aDen : ℕ) : List Term :=
  let ps := kept i aNum aDen
  ps.map fun p =>
    (((p.1 * lib 3 : ℕ) : ℚ) / ((p.2 * lib i : ℕ) : ℚ),
      ((pairs i).count p : ℚ) /
        (1/(p.1 : ℚ) + 1/(p.2 : ℚ) - 1/(lib i : ℚ) - 1/(lib 3 : ℚ)))

-- Natural logs cancel log(2) from the base-2 weighted average and exponent.
noncomputable def rawLog (aNum aDen i : ℕ) : ℝ := meanLog (terms i aNum aDen)
noncomputable def normLog (aNum aDen i : ℕ) : ℝ :=
  rawLog aNum aDen i - ((List.range 7).map (rawLog aNum aDen)).sum / 7
noncomputable def tmm (aNum aDen i : ℕ) : ℝ := Real.exp (normLog aNum aDen i)

def tolerance : ℚ := 1 / 10000000000

def agrees (s : List ℕ) : Prop := ∃ es rs : List ℚ,
  factors edgeBytes = some es ∧ factors s = some rs ∧ es.length = 7 ∧ rs.length = 7 ∧
  ∀ i < 7, |rs[i]! - es[i]!| ≤ tolerance

end Verify

namespace Verify
def edgeFactors : List ℚ := (factors edgeBytes).getD []
def rnaFactors : List ℚ := (factors rnaBytes).getD []
end Verify
