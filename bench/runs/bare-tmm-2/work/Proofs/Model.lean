import Proofs.Intervals

namespace TMM

/-- Read at elaboration time, without rewriting any shipped artifact. -/
def countsBytes : String := include_str ".."/"counts.tsv"
def edgeBytes : String := include_str ".."/"edger-factors.txt"
def rnaBytes : String := include_str ".."/"rnanorm-factors.txt"

def lines (s : String) : List String := s.trimAscii.toString.splitOn "\n"
def matrix : List (List Nat) := (lines countsBytes).map fun s =>
  (s.splitOn "\t").map String.toNat!
def decimal (s : String) : ℚ :=
  let p := s.splitOn "."
  let a := p[0]!
  let b := p[1]!
  ((a ++ b).toNat! : ℚ) / 10 ^ b.length

def edge : List ℚ := (lines edgeBytes).map decimal
def rna : List ℚ := (lines rnaBytes).map decimal

def column (s : Nat) : List Nat := matrix.map fun r => r[s]!
def library (s : Nat) : Nat := (column s).sum

/-- R type-7 / scipy interpolated 75th percentile after all-zero removal.
For 454 rows its zero-based index is 339.75. -/
def upperQuartile (s : Nat) : ℚ :=
  let c := (column s).mergeSort (· ≤ ·)
  ((c[339]! : ℚ) + 3*c[340]!) / 4 / library s

def refDistance (s : Nat) : ℚ :=
  |upperQuartile s - ((List.range 7).map upperQuartile).sum / 7|

/-- First minimizer; indices throughout are zero-based. -/
def reference : Nat := (List.range 7).foldl
  (fun best i => if refDistance i < refDistance best then i else best) 0

def pairs (s : Nat) : List (Nat × Nat) :=
  (matrix.map fun r => (r[s]!, r[reference]!)).filter fun p => 0 < p.1 && 0 < p.2

/-- Twice the average rank; this preserves exact ties without fractional ranks. -/
def twiceRank (keys : List ℚ) (q : ℚ) : Nat :=
  2 * (keys.filter (· < q)).length + (keys.filter (· == q)).length + 1

def mKey (p : Nat × Nat) : ℚ := (p.1 : ℚ) / p.2
def aKey (p : Nat × Nat) : ℚ := (p.1 : ℚ) * p.2

/-- Monotonicity of log makes ratio and product keys sufficient for exact ranks.
Defaults trim 30% of each M tail and 5% of each A tail; keep their intersection. -/
def kept (s : Nat) : List (Nat × Nat) :=
  let ps := pairs s
  let n := ps.length
  let ml := n*3/10+1
  let al := n/20+1
  let mk := ps.map mKey
  let ak := ps.map aKey
  ps.filter fun p =>
    let rm := twiceRank mk (mKey p)
    let ra := twiceRank ak (aKey p)
    2*ml ≤ rm && rm ≤ 2*(n+1-ml) && 2*al ≤ ra && ra ≤ 2*(n+1-al)

/-- Inverse asymptotic binomial variance. -/
def weight (s : Nat) (p : Nat × Nat) : ℚ :=
  1 / (1/(p.1 : ℚ) + 1/(p.2 : ℚ) - 1/(library s : ℚ) - 1/(library reference : ℚ))

def terms (s : Nat) : List (ℚ × ℚ) :=
  let ps := kept s
  let w := (ps.map (weight s)).sum
  ps.map fun p => (weight s p / w,
    (p.1 : ℚ) * library reference / ((p.2 : ℚ) * library s))

/-- A linear combination of natural logarithms, with exact rational coefficients.
Using ln rather than log2 cancels the base change in 2^(weighted M). -/
noncomputable def linearValue : List (ℚ × ℚ) → ℝ
  | [] => 0
  | t :: ts => (t.1 : ℝ) * Real.log (t.2 : ℝ) + linearValue ts

def linearBox : List (ℚ × ℚ) → Box
  | [] => Box.point 0
  | t :: ts => ((logBox 16 t.2).scale t.1).add (linearBox ts)

def linearValid (ts : List (ℚ × ℚ)) : Bool :=
  ts.all fun t => decide (0 ≤ t.1) && logValid 16 t.2

lemma linear_sound (ts : List (ℚ × ℚ)) (h : linearValid ts = true) :
    (linearBox ts).Holds (linearValue ts) := by
  induction ts with
  | nil => exact ⟨by norm_num [linearBox, Box.Holds, Box.point, linearValue],
                  by norm_num [linearBox, Box.Holds, Box.point, linearValue]⟩
  | cons t ts ih =>
    simp only [linearValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact add_sound (scale_sound t.1 h.1.1 (logBox_sound 16 t.2 h.1.2))
      (ih h.2)

noncomputable def logRaw (s : Nat) : ℝ := linearValue (terms s)
def rawBox (s : Nat) : Box := linearBox (terms s)

noncomputable def sumLogs : List Nat → ℝ
  | [] => 0
  | s :: ss => logRaw s + sumLogs ss

def sumBoxes : List Nat → Box
  | [] => Box.point 0
  | s :: ss => (rawBox s).add (sumBoxes ss)

lemma sum_sound (ss : List Nat) (h : ∀ s ∈ ss, linearValid (terms s) = true) :
    (sumBoxes ss).Holds (sumLogs ss) := by
  induction ss with
  | nil => exact ⟨by norm_num [sumBoxes, Box.Holds, Box.point, sumLogs],
                  by norm_num [sumBoxes, Box.Holds, Box.point, sumLogs]⟩
  | cons s ss ih =>
    exact add_sound (linear_sound (terms s) (h s (by simp)))
      (ih (fun t ht => h t (by simp [ht])))

noncomputable def centeredLog (s : Nat) : ℝ := logRaw s - (1/7 : ℝ) * sumLogs (List.range 7)
def centeredBox (s : Nat) : Box :=
  (rawBox s).add (((sumBoxes (List.range 7)).scale (1/7)).neg)
noncomputable def factor (s : Nat) : ℝ := Real.exp (centeredLog s)

/-- This is the precision selected for both R1 and R2, in absolute factor units. -/
def tolerance : ℚ := 1 / 10^10

/-- Required facts are recomputed from the embedded input, not assumed as certificates. -/
theorem input_shape : matrix.length = 454 ∧
    (matrix.all fun r => r.length == 7) = true ∧
    (matrix.all fun r => r.any (0 < ·)) = true := by native_decide

theorem library_sizes : (List.range 7).map library = [1261,621,755,1097,1916,1136,1219] := by
  native_decide

theorem reference_is_fourth : reference = 3 := by native_decide

theorem positive_upper_quartiles : ((List.range 7).all fun s =>
    decide (1 / (10^20 : ℚ) < upperQuartile s)) = true := by native_decide

theorem positive_pair_counts : (List.range 7).map (fun s => (pairs s).length) =
    [244,195,205,300,259,244,227] := by native_decide

theorem exact_kept_counts : (List.range 7).map (fun s => (kept s).length) =
    [63,79,76,283,89,95,79] := by native_decide

theorem all_terms_valid : ((List.range 7).all fun s => linearValid (terms s)) = true := by
  native_decide

lemma terms_valid (s : Nat) (h : s < 7) : linearValid (terms s) = true :=
  List.all_eq_true.mp all_terms_valid s (List.mem_range.mpr h)

lemma centered_sound (s : Nat) (h : s < 7) : (centeredBox s).Holds (centeredLog s) := by
  have hh := add_sound (linear_sound (terms s) (terms_valid s h))
    (neg_sound (scale_sound (1/7) (by norm_num)
      (sum_sound (List.range 7) (fun t ht => terms_valid t (List.mem_range.mp ht)))))
  simpa [centeredBox, centeredLog, rawBox, logRaw, sub_eq_add_neg] using hh

/-- All finite A values clear the default Acutoff, so no additional rows are removed. -/
def aRatio (s : Nat) (p : Nat × Nat) : ℚ :=
  (p.1 : ℚ) * p.2 / ((library s : ℚ) * library reference)

theorem cutoff_check : ((List.range 7).all fun s => (pairs s).all fun p =>
    logValid 32 (aRatio s p) && decide (-30 < (logBox 32 (aRatio s p)).lo)) = true := by
  native_decide

theorem log_two_lower_check : (1/2 : ℚ) ≤ (baseLog 2).lo := by native_decide

noncomputable def aValue (s : Nat) (p : Nat × Nat) : ℝ :=
  Real.log (aRatio s p : ℝ) / (2 * Real.log 2)

theorem default_Acutoff_inactive (s : Fin 7) (p : Nat × Nat) (hp : p ∈ pairs s) :
    (-10^10 : ℝ) < aValue s p := by
  have hc := List.all_eq_true.mp (List.all_eq_true.mp cutoff_check s
    (List.mem_range.mpr s.isLt)) p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hb := logBox_sound 32 (aRatio s p) hc.1
  have hn : (-30 : ℝ) < Real.log (aRatio s p : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hc.2) hb.1
  have htwo := (baseLog_sound 2 (by norm_num) (by norm_num)).1
  norm_num only [Rat.cast_ofNat] at htwo
  have hhalf : (((1/2 : ℚ) : ℝ)) ≤ ((baseLog 2).lo : ℝ) := by
    exact_mod_cast log_two_lower_check
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hhalf
  have hd : 0 < 2 * Real.log 2 := by linarith
  apply (lt_div_iff₀ hd).mpr
  nlinarith

/-- The two sample-1 rows involved in the R/Python A-rounding discrepancy. -/
theorem A_boundary_tie :
    (matrix[162]!)[0]! = 8 ∧ (matrix[162]!)[3]! = 13 ∧
    (matrix[354]!)[0]! = 13 ∧ (matrix[354]!)[3]! = 8 ∧
    twiceRank ((pairs 0).map aKey) 104 = 465 ∧
    2 * ((pairs 0).length + 1 - ((pairs 0).length/20+1)) = 464 := by
  native_decide

end TMM
