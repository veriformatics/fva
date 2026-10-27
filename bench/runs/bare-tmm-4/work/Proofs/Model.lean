import Proofs.Intervals
import Proofs.Parsing

namespace Verification
/-- Library sizes are column sums of the complete input matrix. -/
def librarySizes (counts : List (List ℕ)) : Fin 7 → ℚ :=
  fun i => ((counts.map fun row => row.getD i.val 0).sum : ℕ)

/-- Exact-real TMM data for a retained gene: (inverse variance, expression ratio).
Gene indices in the replay trace are one-based. Reference sample is column 4.
-/
def geneTerm (counts : List (List ℕ)) (i : Fin 7) (gene : ℕ) : ℚ × ℚ :=
  let row := counts.getD (gene-1) []
  let o : ℚ := row.getD i.val 0
  let r : ℚ := row.getD 3 0
  let lib := librarySizes counts
  (1 / (1/o - 1/lib i + 1/r - 1/lib 3), (o * lib 3) / (r * lib i))

/-- Weighted mean coefficients normalized to sum to one. -/
def selectedTerms (counts : List (List ℕ)) (i : Fin 7) (genes : List ℕ) : List (ℚ × ℚ) :=
  let terms := genes.map (geneTerm counts i)
  let weight := (terms.map Prod.fst).sum
  terms.map fun t => (t.1 / weight, t.2)

/-- Type-7 75th percentile on this 454-gene matrix, divided by library size. -/
def upperQuartiles (counts : List (List ℕ)) : Fin 7 → ℚ := fun i =>
  let col : List ℕ := (counts.map fun row => row.getD i.val 0).insertionSort (· ≤ ·)
  (((col.getD 339 0 : ℚ) + 3 * (col.getD 340 0 : ℚ)) / 4) / librarySizes counts i
end Verification

namespace Verification
noncomputable def rationalValue (ts : List (ℚ × ℚ)) : ℝ :=
  (ts.map fun t => (t.1 : ℝ) * Real.log (t.2 : ℝ)).sum

lemma value_projection (ts : List Term) :
    value ts = rationalValue (ts.map fun t => (t.1, t.2.q)) := by
  simp [value, rationalValue, List.map_map, Function.comp_def]

noncomputable def selectedRaw (counts : List (List ℕ)) (masks : Fin 7 → List ℕ)
    (i : Fin 7) : ℝ := rationalValue (selectedTerms counts i (masks i))

noncomputable def selectedTMM (counts : List (List ℕ)) (masks : Fin 7 → List ℕ)
    (i : Fin 7) : ℝ := factor (selectedRaw counts masks) i
end Verification
