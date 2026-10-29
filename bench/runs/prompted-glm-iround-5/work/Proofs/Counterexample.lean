import Init

namespace Iround

-- Exact value of binary64 0x3fdfffffffffffff (0x1.fffffffffffffp-2).
def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984

def inDomain : Prop :=
  0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator

-- Multiplication by the positive denominator preserves distance comparisons.
def nearest (result : Int) : Prop :=
  ∀ candidate : Int,
    (numerator - result * denominator).natAbs ≤
    (numerator - candidate * denominator).natAbs

theorem r1_counterexample : 0 < denominator ∧ inDomain ∧ ¬ nearest 1 := by
  refine ⟨by decide, by unfold inDomain; decide, ?_⟩
  intro h
  have bad := h 0
  exact (by decide : ¬ ((numerator - 1 * denominator).natAbs ≤
    (numerator - 0 * denominator).natAbs)) bad

end Iround

#print axioms Iround.r1_counterexample
