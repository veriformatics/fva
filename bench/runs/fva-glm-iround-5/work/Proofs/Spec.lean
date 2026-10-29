import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- R1 fails: input bits 0x3fdfffffffffffff represent the finite number
0.5 - 2^(-54), in the required interval. Zero is strictly nearer than one,
but the shipped artifact always returns one, without trapping. -/
def r1_counterexample : Prop :=
  let bits : BitVec 64 := 0x3fdfffffffffffff
  let x := ofBits f64fmt bits
  x.IsNum ∧
  x.toReal f64fmt = (1 : ℝ) / 2 - 1 / 18014398509481984 ∧
  0 ≤ x.toReal f64fmt ∧ x.toReal f64fmt ≤ 2147483647 ∧
  |x.toReal f64fmt - 0| < |x.toReal f64fmt - 1| ∧
  Returns Lifted.module "iround" [.f64 bits] [.i32 1]

end Proofs
