import Std

/-!
Verification of the ORIGINAL, unmodified avg_floor implementation.
The requirements are false. This file proves the exact correctness domain
and counterexamples, not an unconditional correctness theorem.
-/
namespace AvgFloor

abbrev I32 := BitVec 32

def intMin : Int := -2147483648
def intMax : Int := 2147483647

def FitsI32 (x : Int) : Prop := intMin ≤ x ∧ x ≤ intMax
  deriving Decidable

/-- Unbounded integer arithmetic; `/ 2` is Euclidean division (floor here). -/
def specification (a b : I32) : Int := (a.toInt + b.toInt) / 2

/-- The two WebAssembly operations emitted for `(a + b) >> 1`. -/
def wasmAvg (a b : I32) : I32 := (a + b).sshiftRight 1

theorem input_range (a : I32) : FitsI32 a.toInt := by
  have lo := BitVec.le_toInt a
  have hi := BitVec.toInt_lt (x := a)
  change -2147483648 ≤ a.toInt at lo
  change a.toInt < 2147483648 at hi
  change -2147483648 ≤ a.toInt ∧ a.toInt ≤ 2147483647
  omega

/-- Quantifying over I32 covers every mathematical signed-32-bit input. -/
theorem encoding_covers_signed_inputs (a : Int) (h : FitsI32 a) :
    (BitVec.ofInt 32 a).toInt = a := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · exact h.1
  · have hi := h.2
    change a ≤ 2147483647 at hi
    change a < 2147483648
    omega

/-- An inequality characterization avoids relying on the name "floor". -/
theorem specification_is_floor (a b : I32) :
    2 * specification a b ≤ a.toInt + b.toInt ∧
      a.toInt + b.toInt < 2 * (specification a b + 1) := by
  unfold specification
  omega

theorem specification_unique (a b : I32) (r : Int) :
    (2 * r ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 * (r + 1)) ↔
      r = specification a b := by
  unfold specification
  omega

theorem specification_fits (a b : I32) : FitsI32 (specification a b) := by
  have ha := input_range a
  have hb := input_range b
  simp only [FitsI32, intMin, intMax, specification] at *
  omega

/-- The exact all-input arithmetic meaning, including wrapped additions. -/
theorem wasmAvg_toInt (a b : I32) :
    (wasmAvg a b).toInt = (a.toInt + b.toInt).bmod 4294967296 / 2 := by
  simp only [wasmAvg, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow,
    BitVec.toInt_add]
  rfl

theorem wrapped_sum (a b : I32) :
    (a.toInt + b.toInt).bmod 4294967296 =
      if a.toInt + b.toInt < intMin then a.toInt + b.toInt + 4294967296
      else if intMax < a.toInt + b.toInt then a.toInt + b.toInt - 4294967296
      else a.toInt + b.toInt := by
  have ha := input_range a
  have hb := input_range b
  simp only [FitsI32, intMin, intMax] at *
  simp only [Int.bmod]
  omega

/-- Overflow changes the answer by exactly 2^31 in either direction. -/
theorem all_input_behavior (a b : I32) :
    (wasmAvg a b).toInt =
      if a.toInt + b.toInt < intMin then specification a b + 2147483648
      else if intMax < a.toInt + b.toInt then specification a b - 2147483648
      else specification a b := by
  rw [wasmAvg_toInt, wrapped_sum]
  unfold specification
  split <;> (try split) <;> omega

/-- Necessary AND sufficient condition; not merely a sufficient precondition. -/
theorem correct_iff_no_overflow (a b : I32) :
    (wasmAvg a b).toInt = specification a b ↔ FitsI32 (a.toInt + b.toInt) := by
  rw [all_input_behavior]
  simp only [FitsI32]
  split <;> (try split) <;> omega

theorem correct_when_sum_fits (a b : I32) (h : FitsI32 (a.toInt + b.toInt)) :
    (wasmAvg a b).toInt = specification a b :=
  (correct_iff_no_overflow a b).mpr h

/-- Partial C model: signed addition must be representable. Arithmetic right
shift is the target-specific choice, not a claim about every C implementation. -/
def cTargetEval (a b : I32) : Option Int :=
  if FitsI32 (a.toInt + b.toInt) then some ((a.toInt + b.toInt) >>> 1)
  else none

theorem c_defined_iff (a b : I32) :
    (cTargetEval a b).isSome = true ↔ FitsI32 (a.toInt + b.toInt) := by
  unfold cTargetEval
  split <;> simp_all

theorem c_correct_when_defined (a b : I32) (r : Int)
    (h : cTargetEval a b = some r) : r = specification a b := by
  unfold cTargetEval at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp [specification, Int.shiftRight_eq_div_pow]
  · contradiction

theorem c_wasm_agree_when_defined (a b : I32) (r : Int)
    (h : cTargetEval a b = some r) : (wasmAvg a b).toInt = r := by
  have hf : FitsI32 (a.toInt + b.toInt) := (c_defined_iff a b).mp (by simp [h])
  rw [correct_when_sum_fits a b hf, c_correct_when_defined a b r h]

def maxInput : I32 := BitVec.ofInt 32 2147483647
def minInput : I32 := BitVec.ofInt 32 (-2147483648)

theorem max_counterexample :
    (wasmAvg maxInput maxInput).toInt = -1 ∧
    specification maxInput maxInput = 2147483647 := by decide

theorem min_counterexample :
    (wasmAvg minInput minInput).toInt = 0 ∧
    specification minInput minInput = -2147483648 := by decide

theorem max_plus_one_counterexample :
    (wasmAvg maxInput 1).toInt = -1073741824 ∧
    specification maxInput 1 = 1073741824 := by decide

theorem negative_odd_example :
    (wasmAvg (BitVec.ofInt 32 (-1)) 0).toInt = -1 ∧
    specification (BitVec.ofInt 32 (-1)) 0 = -1 := by decide

theorem c_overflow_counterexample : cTargetEval maxInput maxInput = none := by decide

def R1 : Prop := ∀ a b : I32, (wasmAvg a b).toInt = specification a b

/-- The part of R2 that specifically requires correctness on overflowing sums. -/
def OverflowRequirement : Prop := ∀ a b : I32,
  ¬ FitsI32 (a.toInt + b.toInt) → (wasmAvg a b).toInt = specification a b

theorem not_R1 : ¬ R1 := by
  intro h
  have hc := h maxInput maxInput
  rw [max_counterexample.1, max_counterexample.2] at hc
  contradiction

theorem not_overflow_requirement : ¬ OverflowRequirement := by
  intro h
  have hc := h maxInput maxInput (by decide)
  rw [max_counterexample.1, max_counterexample.2] at hc
  contradiction

end AvgFloor
