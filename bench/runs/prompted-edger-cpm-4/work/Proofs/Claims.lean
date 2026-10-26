import Proofs.Observed

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

namespace Verification

-- Positive, normal IEEE-754 binary64: exponent, implicit leading bit, scale.
-- The predicate excludes sign bits, zero, subnormal values, infinity and NaN.
def positiveNormal (bits : Nat) : Prop :=
  0 < bits / 2^52 ∧ bits / 2^52 < 2047

def normalRatio (bits : Nat) : Nat × Nat :=
  let e := bits / 2^52
  ((2^52 + bits % 2^52) * 2^(e - 1075), 2^(1075 - e))

-- The actual observation is infinity although the exact target is representable.
theorem r1_counterexample :
    positiveNormal Observed.countBits ∧ positiveNormal Observed.libraryBits ∧
    normalRatio Observed.countBits = (2^1023, 1) ∧
    normalRatio Observed.libraryBits = (2^1023, 1) ∧
    (0 < (2^1023 : Nat)) ∧
    (2^1023 : Nat) / 2^1023 * 1000000 = 1000000 ∧
    positiveNormal Observed.targetBits ∧
    (normalRatio Observed.targetBits).1 = 1000000 * (normalRatio Observed.targetBits).2 ∧
    Observed.outputBits = 0x7ff0000000000000 ∧
    ¬ positiveNormal Observed.outputBits ∧ Observed.outputBits ≠ Observed.targetBits := by
  unfold positiveNormal
  decide

-- R2's biconditional, instantiated with the measured gate count and result.
theorem r2_counterexample :
    Observed.geneCount = 10 ∧ Observed.minCount = 10 ∧
    Observed.qualifying = 1 ∧ Observed.required = 1 ∧ Observed.kept = false ∧
    ¬ (Observed.kept = true ↔ Observed.required ≤ Observed.qualifying) := by
  decide

end Verification

#print axioms Verification.r1_counterexample
#print axioms Verification.r2_counterexample
