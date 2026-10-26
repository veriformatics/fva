import FVATest.Subjects.Tmm.Rel
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# TMM in exact arithmetic (reviewed; contract U14 S3)

edgeR's `calcNormFactors(method = "TMM")` with its default arguments (`calcNormFactors.Rd`,
Robinson and Oshlack 2010), computed exactly: ranks compare exact rationals with R's average
ranks for ties, the trims are 30 % of the log-ratios and 5 % of the abundances, the log-ratios
are real base-2 logarithms. The documentation leaves tie handling open (rubric addendum
2026-10-26 (2)): this is one named reading of it, "exact average-rank TMM".
-/

namespace Subjects.Tmm

open FVA.Cert

/-- A count matrix as text: one row per line, its counts in decimal separated by tabs (byte 9). -/
def countsText (rows : List (List Nat)) : List UInt8 :=
  rows.flatMap fun r => List.intercalate [9] (r.map decimal) ++ [10]

/-- Column `j`. -/
def col (rows : List (List Nat)) (j : Nat) : List Nat := rows.map (·.getD j 0)

/-- R's `rank` with averaged ties (1-based): the values below `x`, plus the mean position of the
values equal to it. -/
def avgRank (xs : List ℚ) (x : ℚ) : ℚ :=
  (xs.filter (· < x)).length + ((xs.filter (· = x)).length + 1) / 2

/-- R's default `quantile` (type 7) of `xs` at probability `p`. -/
def quantile7 (xs : List Nat) (p : ℚ) : ℚ :=
  let s := xs.mergeSort (· ≤ ·)
  let h := ((s.length - 1 : Nat) : ℚ) * p
  let lo := h.floor.toNat
  s.getD lo 0 + (h - lo) * ((s.getD (lo + 1) (s.getD lo 0) : ℚ) - s.getD lo 0)

/-- The genes counted in both libraries, as (library, reference) count pairs. -/
def tmmGenes (obs ref : List Nat) : List (Nat × Nat) :=
  (obs.zip ref).filter fun x => 0 < x.1 ∧ 0 < x.2

/-- A gene's ratio of proportions, `2` to the power of its log-ratio M. -/
def tmmM (nO nR : Nat) (x : Nat × Nat) : ℚ := (x.1 * nR : ℚ) / (nO * x.2)

/-- A gene's product of proportions, which orders genes by their abundance A. -/
def tmmA (nO nR : Nat) (x : Nat × Nat) : ℚ := (x.1 * x.2 : ℚ) / (nO * nR)

/-- A gene's delta-method variance of its log-ratio. -/
def tmmV (nO nR : Nat) (x : Nat × Nat) : ℚ :=
  ((nO - x.1 : ℚ) / (nO * x.1)) + ((nR - x.2 : ℚ) / (nR * x.2))

/-- The genes inside both trims: average ranks of M within the middle 40 % (30 % off each end)
and of A within the middle 90 % (5 % off each end), the trim counts `⌊n · 0.3⌋ + 1` and
`⌊n · 0.05⌋ + 1` as edgeR computes them. -/
def tmmKeep (obs ref : List Nat) (nO nR : Nat) : List (Nat × Nat) :=
  let g := tmmGenes obs ref
  let n := g.length
  let loL : ℚ := ⌊(n : ℚ) * 3 / 10⌋ + 1
  let loS : ℚ := ⌊(n : ℚ) / 20⌋ + 1
  let ms := g.map (tmmM nO nR)
  let as := g.map (tmmA nO nR)
  g.filter fun x => decide (loL ≤ avgRank ms (tmmM nO nR x) ∧
    avgRank ms (tmmM nO nR x) ≤ n + 1 - loL ∧ loS ≤ avgRank as (tmmA nO nR x) ∧
      avgRank as (tmmA nO nR x) ≤ n + 1 - loS)

/-- `.calcFactorTMM` of library `obs` against reference `ref` (library sizes `nO`, `nR`) as a
base-2 logarithm: the inverse-variance weighted mean of the kept genes' log-ratios; 0 when every
log-ratio is below 10⁻⁶ in size (edgeR returns factor 1), and 0 when the trims keep no gene (edgeR:
`NaN`, then 0; here `x / 0 = 0`). -/
noncomputable def tmmLog2 (obs ref : List Nat) (nO nR : Nat) : ℝ :=
  if ∀ x ∈ tmmGenes obs ref, |Real.logb 2 (tmmM nO nR x)| < 1 / 10 ^ 6 then 0
  else ((tmmKeep obs ref nO nR).map fun x => Real.logb 2 (tmmM nO nR x) / tmmV nO nR x).sum /
    ((tmmKeep obs ref nO nR).map fun x => (1 / tmmV nO nR x : ℝ)).sum

/-- Library size: column `j`'s total count. -/
def lib (rows : List (List Nat)) (j : Nat) : Nat := (col rows j).sum

/-- Column `j`'s upper quartile per read. -/
def f75 (rows : List (List Nat)) (j : Nat) : ℚ := quantile7 (col rows j) (3 / 4) / lib rows j

/-- The matrix the factors are defined on: rows of `k ≥ 2` counts, no all-zero row, every library
nonempty and below 2⁵³ reads, and a nondegenerate upper quartile (edgeR's `median(f75) < 1e-20`
fallback inactive). Below 2⁵³ reads edgeR's A cutoff (`Acutoff = -1e10`) drops no gene: a counted
gene's A is at least −53 (`acutoff_inactive`), so `tmmGenes` omits it. -/
def Profile (rows : List (List Nat)) (k : Nat) : Prop :=
  2 ≤ k ∧ (∀ r ∈ rows, r.length = k ∧ ∃ c ∈ r, 0 < c) ∧
    ∀ j < k, 0 < lib rows j ∧ lib rows j < 2 ^ 53 ∧ 1 / 10 ^ 20 ≤ f75 rows j

/-- The reference sample: the one whose upper quartile per read is nearest the mean upper quartile
(the first on ties). -/
def tmmRef (rows : List (List Nat)) (k : Nat) : Nat :=
  let mean : ℚ := ((List.range k).map (f75 rows)).sum / k
  (List.range k).foldl (fun b j => if |f75 rows j - mean| < |f75 rows b - mean| then j else b) 0

/-- The exact TMM factors of a `Profile` matrix with `k` samples: each sample's `tmmLog2` against
the reference sample, centred so the factors multiply to one. -/
noncomputable def exactTMM (rows : List (List Nat)) (k : Nat) : List ℝ :=
  let r := tmmRef rows k
  let l (j : Nat) : ℝ := tmmLog2 (col rows j) (col rows r) (lib rows j) (lib rows r)
  let center : ℝ := ((List.range k).map l).sum / k
  (List.range k).map fun j => (2 : ℝ) ^ (l j - center)

/-- Each value in `ys` is within relative `ε` of the value in `xs` at its position. -/
def WithinRel (ε : ℚ) (xs : List ℝ) (ys : List ℚ) : Prop :=
  ys.length = xs.length ∧ ∀ p ∈ xs.zip ys, |(p.2 : ℝ) - p.1| ≤ ε * p.1

/-- The output `o` (a factor file) does not hold the exact average-rank TMM factors of the count
matrix `i` to relative 10⁻³: `i` is a `Profile` count matrix and `o` a decimal file, and under
every reading `o` has the wrong number of factors or some factor misses its exact value by more
than 10⁻³ of it. -/
def RefutesExactAverageTMM (i o : List UInt8) : Prop :=
  (∃ rows k xs, i = countsText rows ∧ Profile rows k ∧ o = decFile xs) ∧
    ∀ rows k xs, i = countsText rows → Profile rows k → o = decFile xs →
      ¬ WithinRel (1 / 1000) (exactTMM rows k) (xs.map decVal)

end Subjects.Tmm
