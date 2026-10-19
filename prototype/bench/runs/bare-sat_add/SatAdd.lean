import Std

/-!
Verification of sat_add.c for the wasm32 ABI: 32-bit int, 64-bit long long.
All integers in specifications are mathematical Lean Ints, not machine additions.
The source-to-model correspondence is manual; see VERIFICATION.md.
-/

namespace SatAdd

def min32 : Int := -2147483648
def max32 : Int := 2147483647

def InInt32 (x : Int) : Prop := min32 ≤ x ∧ x ≤ max32
def InInt64 (x : Int) : Prop := -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807

/-- `(long long)a + b`: the usual arithmetic conversions widen BOTH operands. -/
def wideSum (a b : BitVec 32) : BitVec 64 :=
  a.signExtend 64 + b.signExtend 64

/-- Line-by-line model of the function, including finite-width addition and cast. -/
def cSatAdd (a b : BitVec 32) : BitVec 32 :=
  let s := wideSum a b
  if max32 < s.toInt then BitVec.ofInt 32 max32
  else if s.toInt < min32 then BitVec.ofInt 32 min32
  else BitVec.ofInt 32 s.toInt

/-- Requirement-level specification, independently expressed as a clamp. -/
def spec (a b : Int) : Int := max min32 (min max32 (a + b))

theorem input_bounds (a : BitVec 32) : InInt32 a.toInt := by
  have lo := BitVec.le_toInt a
  have hi := BitVec.toInt_le (x := a)
  constructor <;> simpa [InInt32, min32, max32] using (by assumption)

theorem sum_bounds (a b : BitVec 32) :
    -4294967296 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ 4294967294 := by
  have ha := input_bounds a
  have hb := input_bounds b
  simp only [InInt32, min32, max32] at ha hb
  omega

/-- The addition cannot invoke C signed-overflow undefined behavior. -/
theorem addition_safe (a b : BitVec 32) : InInt64 (a.toInt + b.toInt) := by
  have h := sum_bounds a b
  unfold InInt64
  omega

theorem widening_exact (a : BitVec 32) : (a.signExtend 64).toInt = a.toInt := by
  exact BitVec.toInt_signExtend_of_le (by decide)

/-- The actual 64-bit addition equals the unbounded mathematical sum. -/
theorem wideSum_exact (a b : BitVec 32) :
    (wideSum a b).toInt = a.toInt + b.toInt := by
  rw [wideSum, BitVec.toInt_add, widening_exact, widening_exact]
  apply Int.bmod_eq_of_le <;> have h := addition_safe a b
  all_goals simp only [InInt64] at h; omega

/-- Converting a representable value to int preserves its mathematical value. -/
theorem narrowing_exact (x : Int) (h : InInt32 x) :
    (BitVec.ofInt 32 x).toInt = x := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · simpa [InInt32, min32] using h.1
  · have := h.2
    simp only [max32] at this
    omega

/-- The final cast is reached only when its operand is representable as int. -/
theorem final_cast_safe (a b : BitVec 32)
    (hhi : ¬ max32 < (wideSum a b).toInt)
    (hlo : ¬ (wideSum a b).toInt < min32) :
    InInt32 (wideSum a b).toInt := by
  unfold InInt32
  omega

/-- Every evaluated step of `-2147483647 - 1` is representable as int. -/
theorem lower_constant_safe :
    InInt32 (-2147483647) ∧ InInt32 (-2147483647 - 1) ∧
    (-2147483647 - 1 : Int) = min32 := by
  unfold InInt32 min32 max32
  decide

/-- R1: no saturation when the mathematical sum is representable. -/
theorem R1 (a b : BitVec 32) (h : InInt32 (a.toInt + b.toInt)) :
    (cSatAdd a b).toInt = a.toInt + b.toInt := by
  have hhi : ¬ max32 < a.toInt + b.toInt := by have := h.2; omega
  have hlo : ¬ a.toInt + b.toInt < min32 := by have := h.1; omega
  simp only [cSatAdd, wideSum_exact, ite_eq_right hhi, ite_eq_right hlo]
  exact narrowing_exact _ h

/-- R2: positive overflow saturates to INT_MAX. -/
theorem R2 (a b : BitVec 32) (h : max32 < a.toInt + b.toInt) :
    (cSatAdd a b).toInt = max32 := by
  simp only [cSatAdd, wideSum_exact, ite_eq_left h]
  exact narrowing_exact _ (by unfold InInt32 min32 max32; decide)

/-- R3: negative overflow saturates to INT_MIN. -/
theorem R3 (a b : BitVec 32) (h : a.toInt + b.toInt < min32) :
    (cSatAdd a b).toInt = min32 := by
  have hhi : ¬ max32 < a.toInt + b.toInt := by
    simp only [min32, max32] at *
    omega
  simp only [cSatAdd, wideSum_exact, ite_eq_right hhi, ite_eq_left h]
  exact narrowing_exact _ (by unfold InInt32 min32 max32; decide)

theorem c_correct (a b : BitVec 32) : (cSatAdd a b).toInt = spec a.toInt b.toInt := by
  by_cases hi : max32 < a.toInt + b.toInt
  · rw [R2 a b hi]
    simp only [spec, min32, max32] at *
    omega
  · by_cases lo : a.toInt + b.toInt < min32
    · rw [R3 a b lo]
      simp only [spec, min32, max32] at *
      omega
    · rw [R1 a b (by constructor <;> omega)]
      unfold spec
      omega

/-- Every mathematical int32 value is represented by the bit-vector inputs. -/
theorem all_signed_inputs (a b : Int) (ha : InInt32 a) (hb : InInt32 b) :
    (cSatAdd (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)).toInt = spec a b := by
  rw [c_correct, narrowing_exact a ha, narrowing_exact b hb]

end SatAdd
