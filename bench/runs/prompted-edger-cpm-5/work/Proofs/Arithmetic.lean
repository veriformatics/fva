prelude
import Init.Data.Rat

/- Exact rational certificates for the executable counterexamples.
   No floating-point primitives, native_decide, or execution oracle is used. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

namespace Verification

-- Value of a positive normal binary64 with significand m and exponent e:
-- m / 2^d, where d = 52 - e. All uses below are away from binade edges.
def dyadic (m d : Nat) : Rat := mkRat (Int.ofNat m) (2^d)

-- Strictly inside the nearest-rounding interval for that binary64.
-- Strict inequalities avoid tie-breaking assumptions.
def nearest (x : Rat) (m d : Nat) : Prop :=
  dyadic (2*m-1) (d+1) < x ∧ x < dyadic (2*m+1) (d+1)

theorem r1_exact_and_overflow :
    let c : Rat := (2^1020 : Nat)
    let maxFinite : Rat := (2^1024 - 2^971 : Nat)
    let overflowBoundary : Rat := (2^1024 - 2^970 : Nat)
    0 < c ∧ c ≤ maxFinite ∧ c / c * 1000000 = 1000000 ∧
      overflowBoundary < c * 1000000 := by
  decide +kernel

theorem r2_rounding_intervals :
    nearest ((10 : Rat) * 1000000 / 18) 4772185884444444 33 ∧
    nearest ((10 : Rat) / 18) 5003999585967218 53 ∧
    nearest (dyadic 5003999585967218 53 * 1000000) 4772185884444445 33 ∧
    dyadic 4772185884444444 33 < dyadic 4772185884444445 33 ∧
    (10 : Rat) / 18 * 1000000 = (10 : Rat) * 1000000 / 18 ∧
    (15 : Nat) ≤ 10 + 10 ∧
    dyadic 4772185884444444 33 - (10000000 : Rat) / 18 =
      -mkRat 1 (9 * 2^31) ∧
    dyadic 4772185884444445 33 - dyadic 4772185884444444 33 = dyadic 1 33 := by
  unfold nearest dyadic
  decide +kernel

theorem r2_fractional_sample_threshold :
    (1 : Rat) < 1 + dyadic 1 48 ∧
    1 + dyadic 1 48 - mkRat 1 (10^14) < 1 := by
  unfold dyadic
  decide +kernel

#print axioms r1_exact_and_overflow
#print axioms r2_rounding_intervals
#print axioms r2_fractional_sample_threshold
end Verification
