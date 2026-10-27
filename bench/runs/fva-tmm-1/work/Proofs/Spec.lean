import Proofs.Model
import Proofs.Counts
import Proofs.Edger
import Proofs.Rnanorm

namespace Proofs

/-- R1, at absolute tolerance 1/40 = 0.025, for exact-real default TMM.
This deliberately coarse tolerance is necessary: floating-point tie breaking
changes the selected genes. See tightAccuracyFails for the precision limitation. -/
def R1 : Prop :=
  ∃ xs ds, Counts.blob.data = matrixText xs ∧ Edger.blob.data = factorText ds ∧
    matrixOK xs ∧ ds.length = 7 ∧
    ∀ j ∈ List.range 7, |(decimalValue ds[j]! : ℝ) - tmm xs j 3| ≤ 1 / 40

/-- R2, at absolute tolerance 1/40 = 0.025, for the same exact-real TMM
procedure (30% M trimming, 5% A trimming, inverse-variance weighting,
reference chosen by upper quartile, and geometric-mean rescaling). -/
def R2 : Prop :=
  ∃ xs ds, Counts.blob.data = matrixText xs ∧ Rnanorm.blob.data = factorText ds ∧
    matrixOK xs ∧ ds.length = 7 ∧
    ∀ j ∈ List.range 7, |(decimalValue ds[j]! : ℝ) - tmm xs j 3| ≤ 1 / 40

/-- R3 FAILS: every paired entry of the two shipped files differs by more
than 0.001, hence the files cannot agree to ten decimal places. -/
def R3Fails : Prop :=
  ∃ es rs, Edger.blob.data = factorText es ∧ Rnanorm.blob.data = factorText rs ∧
    es.length = 7 ∧ rs.length = 7 ∧
    ∀ j ∈ List.range 7,
      1 / 1000 < |(decimalValue es[j]! : ℝ) - (decimalValue rs[j]! : ℝ)|

/-- Neither file is accurate to 0.02 at sample 3 relative to the exact-real
TMM model with exact average ranks. This is a limitation of R1/R2's loose
tolerance, not a claim that the files fail to reproduce R/NumPy. -/
def tightAccuracyFails : Prop :=
  ∃ xs es rs,
    Counts.blob.data = matrixText xs ∧ Edger.blob.data = factorText es ∧
    Rnanorm.blob.data = factorText rs ∧ matrixOK xs ∧
    (1 / 50 < |(decimalValue es[2]! : ℝ) - tmm xs 2 3|) ∧
    (1 / 50 < |(decimalValue rs[2]! : ℝ) - tmm xs 2 3|)

end Proofs
