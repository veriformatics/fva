import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- R1 fails: the finite binary64 input immediately below 0.5 is in the required
range, but the artifact always returns 1, although integer 0 is strictly closer.
Its exact value is (2^53 - 1) / 2^54, so this is not an allowed halfway tie. -/
def r1_counterexample : Prop :=
  let b : BitVec 64 := 0x3fdfffffffffffff
  let x := ofBits f64fmt b
  x.IsNum ∧
  x.toReal f64fmt = (9007199254740991 : ℝ) / 18014398509481984 ∧
  0 ≤ x.toReal f64fmt ∧ x.toReal f64fmt ≤ 2147483647 ∧
  Returns Lifted.module "iround" [.f64 b] [.i32 1] ∧
  |x.toReal f64fmt - (0 : ℝ)| < |x.toReal f64fmt - (1 : ℝ)|

end Proofs
