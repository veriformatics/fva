import Init

namespace Counterexample

-- The exact input is numerator / denominator. Distances below are scaled by denominator.
def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984
def output : Int := 1

def Nearest (n d r : Int) : Prop :=
  ∀ m : Int, (n - r * d).natAbs ≤ (n - m * d).natAbs

theorem domain_and_strictly_closer :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    (numerator - 0 * denominator).natAbs < (numerator - output * denominator).natAbs := by
  decide +kernel

theorem r1_counterexample :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    ¬ Nearest numerator denominator output := by
  refine ⟨domain_and_strictly_closer.1, domain_and_strictly_closer.2.1,
    domain_and_strictly_closer.2.2.1, ?_⟩
  intro h
  have bad : ¬ ((numerator - output * denominator).natAbs ≤
      (numerator - 0 * denominator).natAbs) := by
    decide +kernel
  exact bad (h 0)

end Counterexample
