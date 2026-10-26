import Mathlib

/-!
Exact rational certificates for the executed counterexamples. This is NOT a
formalization of the Wasm interpreter or of R. Executions of the unchanged
artifact and R files are checked separately by verification/check.py.
-/
namespace Verification

def idealCPM (c L : ℚ) : ℚ := c / L * 1000000

def kernelBoundary : ℚ := 1193046471111111 / 2147483648

def cutoffQuotient : ℚ := 2501999792983609 / 4503599627370496

def cutoffBoundary : ℚ := 4772185884444445 / 8589934592

def boundaryULP : ℚ := 1 / 8589934592

/-- Decode only positive, normal IEEE-754 binary64 encodings.
    The theorem below uses no zero, subnormal, infinity, NaN, or sign bit. -/
def positiveNormal64 (bits : ℕ) : ℚ :=
  let exponent : ℤ := ((bits / 2^52) % 2048 : ℕ)
  let significand : ℚ := ((2^52 + bits % 2^52 : ℕ) : ℚ)
  significand * (2 : ℚ)^(exponent - 1075)

theorem witness_encodings :
    positiveNormal64 0x4120f4471c71c71c = kernelBoundary ∧
    positiveNormal64 0x4120f4471c71c71d = cutoffBoundary ∧
    positiveNormal64 0x3fe1c71c71c71c72 = cutoffQuotient ∧
    positiveNormal64 0x7fe0000000000000 = (2 : ℚ)^1023 := by
  norm_num [positiveNormal64, kernelBoundary, cutoffBoundary, cutoffQuotient]
  rw [show (1023 : ℕ) = 52 + 971 from rfl, pow_add]
  norm_num

/-- A strict midpoint certificate; no tie-breaking convention is needed. -/
def GridCertificate (x y step : ℚ) : Prop :=
  ∃ k : ℤ, y = (k : ℚ) * step ∧ 0 < step ∧
    y - step / 2 < x ∧ x < y + step / 2

/-- A midpoint certificate makes y uniquely nearest among all grid points. -/
theorem gridCertificate_nearest {x y step : ℚ} (h : GridCertificate x y step) :
    ∀ z : ℤ, (z : ℚ) * step ≠ y → |x - y| < |x - (z : ℚ) * step| := by
  obtain ⟨k, hk, hs, hlo, hhi⟩ := h
  have hnear : |x - y| < step / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  intro z hz
  have hzk : z ≠ k := by
    intro heq
    subst z
    exact hz hk.symm
  rcases lt_or_gt_of_ne hzk with hlt | hgt
  · have hle : z ≤ k - 1 := by omega
    have hcast : (z : ℚ) ≤ (k : ℚ) - 1 := by exact_mod_cast hle
    have hprod : (z : ℚ) * step ≤ y - step := by nlinarith
    have hfar : step / 2 < |x - (z : ℚ) * step| :=
      lt_abs.mpr (Or.inl (by linarith))
    exact hnear.trans hfar
  · have hle : k + 1 ≤ z := by omega
    have hcast : (k : ℚ) + 1 ≤ (z : ℚ) := by exact_mod_cast hle
    have hprod : y + step ≤ (z : ℚ) * step := by nlinarith
    have hfar : step / 2 < |x - (z : ℚ) * step| :=
      lt_abs.mpr (Or.inr (by linarith))
    exact hnear.trans hfar

-- 10 * 1,000,000 is an exactly representable integer. This certifies the
-- following division. The grid spacing at the result's binade is 2^-33.
theorem kernel_rounding :
    GridCertificate (idealCPM 10 18) kernelBoundary boundaryULP := by
  refine ⟨4772185884444444, ?_⟩
  norm_num [idealCPM, kernelBoundary, boundaryULP]

-- The cutoff instead rounds 10/18 first (spacing 2^-53), then multiplies.
theorem cutoff_division_rounding :
    GridCertificate ((10 : ℚ) / 18) cutoffQuotient (1 / 2^53) := by
  refine ⟨5003999585967218, ?_⟩
  norm_num [cutoffQuotient]

theorem cutoff_multiplication_rounding :
    GridCertificate (cutoffQuotient * 1000000) cutoffBoundary boundaryULP := by
  refine ⟨4772185884444445, ?_⟩
  norm_num [cutoffQuotient, cutoffBoundary, boundaryULP]

/-- Signed absolute errors and the absolute relative error of the kernel value. -/
theorem boundary_errors :
    kernelBoundary - idealCPM 10 18 = -1 / 19327352832 ∧
    cutoffBoundary - idealCPM 10 18 = 5 / 77309411328 ∧
    |kernelBoundary - idealCPM 10 18| / idealCPM 10 18 =
      1 / 10737418240000000 ∧
    cutoffBoundary - kernelBoundary = boundaryULP := by
  norm_num [idealCPM, kernelBoundary, cutoffBoundary, boundaryULP]

/-- Relevant decision for two identical samples, default total cutoff 15.
    Exact rational comparison model, without the R tolerance. -/
def keepsTwo (cpm cutoff total : ℚ) : Prop :=
  (2 : ℚ) ≤ (if cutoff ≤ cpm then 2 else 0) ∧ 15 ≤ total

/-- At count 10 in both samples, the mathematical CPM rule keeps the gene;
    the two distinct computed binary64 values make that rule reject it. -/
theorem r2_counterexample :
    keepsTwo (idealCPM 10 18) (idealCPM 10 18) 20 ∧
    ¬ keepsTwo kernelBoundary cutoffBoundary 20 := by
  norm_num [keepsTwo, idealCPM, kernelBoundary, cutoffBoundary]

/-- The R tolerance cannot rescue zero passing samples in this witness.
    These bounds cover any rounded threshold near 2 and total cutoff near 15. -/
theorem r2_tolerance_robust (required totalCutoff : ℚ)
    (hr : 0 < required) (_ht : totalCutoff ≤ 20) :
    (required ≤ (if cutoffBoundary ≤ kernelBoundary then (2 : ℚ) else 0) ∧
      totalCutoff ≤ 20) = False := by
  have h : ¬ cutoffBoundary ≤ kernelBoundary := by
    norm_num [cutoffBoundary, kernelBoundary]
  simp only [h, ↓reduceIte]
  simp only [eq_iff_iff, iff_false, not_and]
  intro hbad
  linarith

def maxFinite : ℚ := (2 - 1 / 2^52) * 2^1023

/-- A finite, exactly representable positive count/library has exact CPM 10^6,
    although the implementation's intermediate product exceeds even 2^1024. -/
theorem r1_overflow_witness :
    0 < (2 : ℚ)^1023 ∧
    (2 : ℚ)^1023 ≤ maxFinite ∧
    idealCPM ((2 : ℚ)^1023) ((2 : ℚ)^1023) = 1000000 ∧
    (2 : ℚ)^1024 < (2 : ℚ)^1023 * 1000000 := by
  have hlast : (2 : ℚ)^1024 < (2 : ℚ)^1023 * 1000000 := by
    rw [show 1024 = 1023 + 1 from rfl, pow_succ]
    exact mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  refine ⟨by positivity, ?_, ?_, hlast⟩
  · norm_num [maxFinite]
  · norm_num [idealCPM]

#print axioms witness_encodings
#print axioms gridCertificate_nearest
#print axioms kernel_rounding
#print axioms cutoff_division_rounding
#print axioms cutoff_multiplication_rounding
#print axioms boundary_errors
#print axioms r2_counterexample
#print axioms r2_tolerance_robust
#print axioms r1_overflow_witness

end Verification
