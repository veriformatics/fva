import Mathlib
import Init.Data.Float.Model

/-!
Concrete arithmetic witnesses, using Lean's *logical* binary64 model.
This file does not formalize Wasm control flow, memory, or the R interpreter.
Verification/check.py separately executes the original binary and R files.
No native_decide, sorry, new axioms, or hardware Float evaluation is used.
-/
namespace Counterexamples

set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev F := Float.Model

/-- Exact rational meaning of a finite binary64; infinity/NaN have no value. -/
def value (f : F) : Option ℚ :=
  match f.unpack with
  | .finite s m e _ => some ((s.apply (Int.ofNat m) : ℚ) * (2 : ℚ) ^ e)
  | .zero _ => some 0
  | _ => none

def million : F := Float.Model.ofNat 1000000
def large : F := Float.Model.ofBits 0x7fe0000000000000

/-- Arithmetic instruction order in the artifact: f64.mul, then f64.div. -/
def raw (c L : F) : F := (c * million) / L

/-- Arithmetic instruction order in the R cutoff expression. -/
def cutoff (c L : F) : F := (c / L) * million

theorem large_value : value large = some ((2 : ℚ) ^ (1023 : ℕ)) := by decide +kernel

theorem large_positive : (0 : ℚ) < 2 ^ (1023 : ℕ) := by positivity

theorem r1_exact :
    (2 : ℚ) ^ (1023 : ℕ) / 2 ^ (1023 : ℕ) * 1000000 = 1000000 := by
  have h : (2 : ℚ) ^ (1023 : ℕ) ≠ 0 := ne_of_gt large_positive
  rw [div_self h, one_mul]

theorem r1_overflow :
    (raw large large).toBits = 0x7ff0000000000000 ∧
    value (raw large large) = none ∧
    value (cutoff large large) = some 1000000 := by decide +kernel

def ten : F := Float.Model.ofNat 10
def thirtySix : F := Float.Model.ofNat 36
def boundaryCPM : ℚ := 1193046471111111 / 4294967296
def boundaryCutoff : ℚ := 4772185884444445 / 17179869184

theorem r2_boundary_bits :
    (raw ten thirtySix).toBits = 0x4110f4471c71c71c ∧
    (cutoff ten thirtySix).toBits = 0x4110f4471c71c71d ∧
    value (raw ten thirtySix) = some boundaryCPM ∧
    value (cutoff ten thirtySix) = some boundaryCutoff := by decide +kernel

/-- Exact signed errors for the count-boundary witness, relative to real CPM. -/
theorem r2_boundary_errors :
    boundaryCPM - (10 / 36 * 1000000 : ℚ) = -1 / 38654705664 ∧
    boundaryCutoff - (10 / 36 * 1000000 : ℚ) = 5 / 154618822656 := by
  norm_num [boundaryCPM, boundaryCutoff]

/-- Both samples meet the exact count threshold and total-count condition;
    neither meets the rounded threshold comparison actually performed. -/
theorem r2_count_boundary :
    (10 / 36 * 1000000 : ℚ) ≥ 10 / 36 * 1000000 ∧
    (2 : ℚ) ≥ 2 ∧ (10 + 10 : ℚ) ≥ 15 ∧
    ¬ (boundaryCPM ≥ boundaryCutoff) := by
  norm_num [boundaryCPM, boundaryCutoff]

def required : F := Float.Model.ofNat 1 + Float.Model.ofBits 0x3cd0000000000000
def tolerance : F := Float.Model.ofBits 0x3d06849b86a12b9b

theorem r2_sample_tolerance :
    value required = some (1 + 1 / (2 : ℚ) ^ (50 : ℕ)) ∧
    (required.toBits = 0x3ff0000000000004) ∧
    (decide (Float.Model.ofNat 1 ≥ required) = false) ∧
    (decide (Float.Model.ofNat 1 ≥ required - tolerance) = true) ∧
    ((20 : ℚ) ≥ 15) := by decide +kernel

theorem r2_required_strictly_above_one :
    (1 : ℚ) < 1 + 1 / 2 ^ (50 : ℕ) := by norm_num

#print axioms large_value
#print axioms large_positive
#print axioms r1_exact
#print axioms r1_overflow
#print axioms r2_boundary_bits
#print axioms r2_boundary_errors
#print axioms r2_count_boundary
#print axioms r2_sample_tolerance
#print axioms r2_required_strictly_above_one

end Counterexamples
