import Mathlib.Tactic.NormNum

set_option maxRecDepth 10000

namespace Certificate

-- Standard binary64 value, restricted to positive finite normal encodings:
-- 0 < b / 2^52 < 2047. Two Nat powers handle either sign of the exponent.
def normal64 (b : Nat) : Rat :=
    ((2^52 + b % 2^52 : Nat) : Rat) / 2^(1075 - b / 2^52) *
      2^(b / 2^52 - 1075)

theorem bit_values :
    normal64 0x7fe0000000000000 = 2^1023 ∧
    normal64 0x4120f4471c71c71c = (1193046471111111 : Rat) / 2147483648 ∧
    normal64 0x4120f4471c71c71d = (4772185884444445 : Rat) / 8589934592 ∧
    0x7ff0000000000000 / 2^52 = (2047 : Nat) ∧
    0x7ff0000000000000 % 2^52 = (0 : Nat) := by
  constructor
  · norm_num [normal64]
    rw [show (4503599627370496 : Rat) = 2^52 by norm_num, ← pow_add]
  · norm_num [normal64]

-- Exact arithmetic for the overflow witness. Runtime output is +infinity.
theorem overflow_target :
    (0 : Rat) < 2^1023 ∧
    (2^1023 : Rat) / 2^1023 * 1000000 = 1000000 := by norm_num

-- Exact arithmetic for the two-sample filtering witness.
theorem boundary_target :
    (10 : Rat) / 18 * 1000000 = 5000000 / 9 ∧
    (10 : Rat) + 10 ≥ 15 := by norm_num

-- Actual CPM and R cutoff, decoded from their binary64 bits.
-- The exact threshold lies strictly between adjacent binary64 values.
theorem boundary_gap :
    (1193046471111111 : Rat) / 2147483648 < 5000000 / 9 ∧
    (5000000 : Rat) / 9 < 4772185884444445 / 8589934592 ∧
    (4772185884444445 : Rat) / 8589934592 -
      1193046471111111 / 2147483648 = 1 / 8589934592 := by norm_num

-- The Wasm result is the correctly rounded ideal CPM at this input:
-- error is 4/9 ulp, less than half an ulp. R's cutoff is 5/9 ulp high.
theorem boundary_error :
    (5000000 : Rat) / 9 - 1193046471111111 / 2147483648 = 1 / 19327352832 ∧
    (1 : Rat) / 19327352832 < (1 / 8589934592) / 2 := by norm_num

end Certificate
