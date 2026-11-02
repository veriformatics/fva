import FVATest.Examples.Planted.Lifted
import FVATest.Examples.Planted.Def
import FVATest.Examples.Planted.Syntax
import FVA.Spec.CAbi

/-! The prototype's planted cheats on `toy.wasm`, as an `fva explain` test bed: each docstring
states what its author means; five statements say something else (`fva trust` fails them all, and
the two with honest statements fail on their missing proofs). No proofs: `fva explain` reads the
statements alone. Adapted from the prototype: the planted macro matches `∀ (x : T), P` with a
written type, so the claims meant to stay honest or false (not vacuous) leave the type to
inference. -/

namespace Examples.Planted

open FVA.Wasm FVA.Wasm.Exec

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` if `x < lo`, else `hi` if `x > hi`, else `x`. -/
@[fva_claim] def clampSpec : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi] [.i32 x]

/-- `gcd(a, b)` on unsigned 32-bit ints: their greatest common divisor (`gcd(a, 0) = a`). -/
@[fva_claim] def gcdSpec : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "gcd" [.i32 a, .i32 b]
    [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

/-- `sum_to(n)` on unsigned 32-bit ints: `0 + 1 + … + (n − 1)`, wrapped to 32 bits. -/
@[fva_claim] def sumToSpec : Prop :=
  ∀ n, Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))]

/-- `sum_to(n)` on unsigned 32-bit ints: `0 + 1 + … + (n − 1)`, wrapped to 32 bits. -/
@[fva_claim] def sumToZero : Prop :=
  ∀ n, Returns Lifted.module "sum_to" [.i32 n] [.i32 0]

/-- `0 + 1 + … + 9 = 45`. -/
@[fva_claim] def sumBelowTen : Prop := sumBelow 10 = 0

/-- `gcd(a, b)` terminates for every pair of 32-bit inputs. -/
@[fva_claim] def gcdTerminates : Prop := ∀ _a _b : BitVec 32, True

/-- `sum_to(n)` returns 7 for every input. -/
@[fva_claim] def sumToSeven : Prop :=
  ∀ (n : BitVec 32), Returns Lifted.module "sum_to" [.i32 n] [.i32 7]

end Examples.Planted
