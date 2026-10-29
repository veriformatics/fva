import Init.Data.Int.Basic
namespace Verification

def numerator : Int := 9007199254740991
def denominator : Int := 18014398509481984
def nearest (n d r : Int) : Prop :=
  ∀ z : Int, (n - d * r).natAbs ≤ (n - d * z).natAbs

theorem input_encoding :
    (0x3fdfffffffffffff : Nat) = 1021 * 2^52 + 4503599627370495 ∧
    numerator = 2^52 + 4503599627370495 ∧ denominator = 2^54 := by decide +kernel

theorem r1_counterexample :
    0 < denominator ∧ 0 ≤ numerator ∧ numerator ≤ 2147483647 * denominator ∧
    ¬ nearest numerator denominator 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro h
  exact (by decide +kernel : ¬ (numerator - denominator * 1).natAbs ≤
    (numerator - denominator * 0).natAbs) (h 0)

theorem strictly_closer :
    (numerator - denominator * 0).natAbs < (numerator - denominator * 1).natAbs := by
  decide +kernel
end Verification
