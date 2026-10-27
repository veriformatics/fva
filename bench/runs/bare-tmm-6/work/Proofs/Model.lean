import Proofs.LogBounds

namespace Verification

-- include_str reads the actual shipped text when this module is elaborated.
def countsBytes : String := include_str ".."/"counts.tsv"
def edgeBytes : String := include_str ".."/"edger-factors.txt"
def rnaBytes : String := include_str ".."/"rnanorm-factors.txt"

def lines (s : String) : List String := (s.splitOn "\n").filter (· != "")
def counts : List (List Nat) := (lines countsBytes).map fun s =>
  (s.splitOn "\t").map fun t => t.toNat?.getD 0

def decimal (s : String) : ℚ :=
  let parts := s.splitOn "."
  let a := parts[0]!.toNat?.getD 0
  let b := parts[1]!
  (a:ℚ) + (b.toNat?.getD 0:ℚ) / (10^b.length:Nat)

def edgeFactors : List ℚ := (lines edgeBytes).map decimal
def rnaFactors : List ℚ := (lines rnaBytes).map decimal

def library (j : Nat) : Nat := (counts.map fun r => r[j]!).sum

def nonzeroRows : List (List Nat) := counts.filter fun r => r.any (· > 0)

def quartile (j : Nat) : ℚ :=
  let xs := (nonzeroRows.map fun r => r[j]!).mergeSort (· ≤ ·)
  let t := (xs.length - 1)*3
  ((xs[t/4]!:ℚ)*(4-t%4) + (xs[t/4+1]!:ℚ)*(t%4)) / 4 / library j

def uqMean : ℚ := ((List.range 7).map quartile).sum / 7

-- Exact reference selected by the documented upper-quartile rule.
def referenceIsFourth : Prop :=
  ∀ j ∈ List.range 7, j ≠ 3 → |quartile 3 - uqMean| < |quartile j - uqMean|
  deriving Decidable

def eligible (j : Nat) : List (List Nat) :=
  nonzeroRows.filter fun r => r[j]! > 0 && r[3]! > 0

def mKey (j : Nat) (r : List Nat) : ℚ := (r[j]!:ℚ) / r[3]!
def aKey (j : Nat) (r : List Nat) : Nat := r[j]! * r[3]!

def rankTwice {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (xs : List α) (x : α) : Nat :=
  2 * (xs.filter (· < x)).length + (xs.filter (· == x)).length + 1

def kept (j : Nat) : List (List Nat) :=
  let xs := eligible j
  let n := xs.length
  let ml := n*3/10+1
  let al := n/20+1
  let ms := xs.map (mKey j)
  let az := xs.map (aKey j)
  xs.filter fun r =>
    let mr := rankTwice ms (mKey j r)
    let ar := rankTwice az (aKey j r)
    2*ml ≤ mr && mr ≤ 2*(n+1-ml) && 2*al ≤ ar && ar ≤ 2*(n+1-al)

def variance (j : Nat) (r : List Nat) : ℚ :=
  ((library j:ℚ) - r[j]!) / ((library j:ℚ)*r[j]!) +
  ((library 3:ℚ) - r[3]!) / ((library 3:ℚ)*r[3]!)

def terms (j : Nat) : List (ℚ × ℚ) :=
  if j == 3 then [] else
  let xs := kept j
  let total := (xs.map fun r => 1 / variance j r).sum
  xs.map fun r => ((1 / variance j r) / total,
    (r[j]!:ℚ) * library 3 / ((r[3]!:ℚ) * library j))

-- Natural logs give the same factor as weighted log2 followed by 2^x.
noncomputable def rawLog (j : Nat) : ℝ :=
  ((terms j).map fun (w,q) => (w:ℝ) * Real.log (q:ℝ)).sum
noncomputable def meanLog : ℝ := (∑ j ∈ Finset.range 7, rawLog j) / 7
noncomputable def factor (j : Nat) : ℝ := Real.exp (rawLog j - meanLog)

end Verification
