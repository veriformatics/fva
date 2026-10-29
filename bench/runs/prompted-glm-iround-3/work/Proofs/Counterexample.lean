namespace Verification

def bits : Nat := 0x3fdfffffffffffff
def p : Nat := 9007199254740991
def q : Nat := 18014398509481984

-- Positive normal binary64: sign, exponent, significand, denominator.
theorem binary64_encoding :
    bits / 2^63 = 0 ∧ (bits / 2^52) % 2048 = 1021 ∧
    2^52 + bits % 2^52 = p ∧ 2^(1023 + 52 - 1021) = q := by
  decide +kernel

-- For x = p/q: domain bounds and distances to 0 and 1, scaled by q.
theorem counterexample_arithmetic :
    0 < p ∧ p < q ∧ p ≤ 2147483647 * q ∧ p < q - p := by
  decide +kernel

end Verification
