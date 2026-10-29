import Proofs.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Numerics.Float

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- R1 fails: input bits 0x3fdfffffffffffff encode the finite number
9007199254740991/18014398509481984 (just below 0.5), inside the required domain.
The artifact always returns 1, although integer 0 is strictly closer than integer 1.
Thus this is not an allowed halfway case. -/
def R1Counterexample : Prop :=
  let x : BitVec 64 := 0x3fdfffffffffffff
  let v := ofBits f64fmt x
  v.IsNum ∧
  v.toReal f64fmt = (9007199254740991 : ℝ) / 18014398509481984 ∧
  0 ≤ v.toReal f64fmt ∧ v.toReal f64fmt ≤ 2147483647 ∧
  |v.toReal f64fmt - 0| < |v.toReal f64fmt - 1| ∧
  Returns Lifted.module "iround" [.f64 x] [.i32 1]

end Proofs
