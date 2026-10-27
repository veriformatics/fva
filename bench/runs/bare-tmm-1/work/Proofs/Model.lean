import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Verification

-- These literals are read from the shipped files by Lean at elaboration time.
def countsBytes : String := include_str "../counts.tsv"
def edgeBytes : String := include_str "../edger-factors.txt"
def rnaBytes : String := include_str "../rnanorm-factors.txt"

-- List/character parsers are transparent to Lean's kernel. The standard
-- optimized String.splitOn/toNat! primitives are not used in proofs.
def lines (s : String) : List (List Char) :=
  (s.toList.splitOn '\n').filter (· != [])
def digits (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
def counts : List (List Nat) := (lines countsBytes).map fun cs =>
  (cs.splitOn '\t').map digits
def decimal (cs : List Char) : ℚ :=
  let p := cs.splitOn '.'
  (digits p[0]! : ℚ) + (digits p[1]! : ℚ) / 10 ^ p[1]!.length

def edge : List ℚ := (lines edgeBytes).map decimal
def rna : List ℚ := (lines rnaBytes).map decimal
noncomputable def tolerance : ℝ := 1 / 10 ^ 10

def column (j : Nat) : List Nat := counts.map (fun r => r[j]!)
def lib (j : Nat) : Nat := (column j).sum

def quartile (j : Nat) : ℚ :=
  let xs := (column j).mergeSort (· ≤ ·)
  let k := 3 * (xs.length - 1)
  ((4 - k % 4 : Nat) * xs[k / 4]! + (k % 4) * xs[k / 4 + 1]! : Nat) / (4 : ℚ)

def uq (j : Nat) : ℚ := quartile j / lib j
def uqMean : ℚ := ((List.range 7).map uq).sum / 7
def distance (j : Nat) : ℚ := |uq j - uqMean|
def reference : Nat := (List.range 7).foldl (fun best j =>
  if distance j < distance best then j else best) 0

abbrev Pair := Nat × Nat

def positivePairs (j : Nat) : List Pair :=
  (counts.map fun r => (r[j]!, r[3]!)).filter (fun p => 0 < p.1 && 0 < p.2)

-- Strict order/equality of exact M values is the order/equality of x/y.
-- For A it is that of x*y. Library sizes are fixed positive constants.
def mLt (p q : Pair) : Bool := p.1 * q.2 < q.1 * p.2
def mEq (p q : Pair) : Bool := p.1 * q.2 == q.1 * p.2
def aLt (p q : Pair) : Bool := p.1 * p.2 < q.1 * q.2
def aEq (p q : Pair) : Bool := p.1 * p.2 == q.1 * q.2

-- Twice the 1-based average rank; no rounding of half-integer ranks.
def twiceRank (lt eq : Pair → Pair → Bool) (ps : List Pair) (p : Pair) : Nat :=
  2 * (ps.filter (fun q => lt q p)).length +
    (ps.filter (fun q => eq q p)).length + 1

def selected (j : Nat) (aNumer aDenom : Nat := 1) : List Pair :=
  let ps := positivePairs j
  let n := ps.length
  let ml := n * 3 / 10 + 1
  let mh := n - n * 3 / 10
  let al := n * aNumer / aDenom + 1
  let ah := n - n * aNumer / aDenom
  ps.filter fun p =>
    let m := twiceRank mLt mEq ps p
    let a := twiceRank aLt aEq ps p
    2 * ml ≤ m && m ≤ 2 * mh && 2 * al ≤ a && a ≤ 2 * ah

def ratio (j : Nat) (p : Pair) : ℚ :=
  (p.1 * lib 3 : Nat) / (p.2 * lib j : ℚ)
def weight (j : Nat) (p : Pair) : ℚ :=
  1 / (((lib j - p.1 : Nat) : ℚ) / (lib j * p.1 : Nat) +
    ((lib 3 - p.2 : Nat) : ℚ) / (lib 3 * p.2 : Nat))

noncomputable def weightedLog (j : Nat) (ps : List Pair) : ℝ :=
  (ps.map (fun p => (weight j p : ℝ) * Real.log (ratio j p))).sum /
    (ps.map (fun p => (weight j p : ℝ))).sum

-- Natural logarithms cancel the base-2 conversion and subsequent 2^M.
-- Self comparison returns raw factor 1, hence log 0.
noncomputable def rawLog (aNumer aDenom j : Nat) : ℝ :=
  if j = 3 then 0 else weightedLog j (selected j aNumer aDenom)
noncomputable def meanLog (aNumer aDenom : Nat) : ℝ :=
  ((List.range 7).map (rawLog aNumer aDenom)).sum / 7
noncomputable def factor (aNumer aDenom j : Nat) : ℝ :=
  Real.exp (rawLog aNumer aDenom j - meanLog aNumer aDenom)

-- This bound is rational and comes with an analytic proof in Bounds.lean.
def logLower (q : ℚ) : ℚ :=
  let z := (q - 1) / (q + 1)
  2 * (z + z^3 / 3 + z^5 / 5) - 2 * |z|^7 / (1 - z^2)

end Verification
