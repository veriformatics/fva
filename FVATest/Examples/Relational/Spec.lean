import FVATest.Examples.Relational.Lifted
import FVA.Spec.CAbi

/-! Relational claims about `toy.wasm` (D18): their examples are rows of inputs, the binary's
results and whether the claim's condition holds on them. No proofs: `fva explain` reads the
statements alone, and `sumToAtMost` is false (`sum_to(4) = 6`). -/

namespace Examples.Relational

open FVA.Wasm FVA.Wasm.Exec

/-- With `lo ≤ hi` (signed), `clamp(x, lo, hi)` lies in `[lo, hi]`. -/
@[fva_claim] def clampInRange : Prop :=
  ∀ x lo hi r : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi] [.i32 r] →
    lo.sle hi → lo.sle r ∧ r.sle hi

/-- `sum_to(n)` never exceeds `n` (unsigned). -/
@[fva_claim] def sumToAtMost : Prop :=
  ∀ n r : BitVec 32, Returns Lifted.module "sum_to" [.i32 n] [.i32 r] → r ≤ n

/-- The greatest common divisor does not depend on the order of its arguments. -/
@[fva_claim] def gcdComm : Prop :=
  ∀ a b : BitVec 32, Nat.gcd a.toNat b.toNat = Nat.gcd b.toNat a.toNat

end Examples.Relational
