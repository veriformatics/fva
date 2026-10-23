import FVATest.Examples.Toy.Lifted
import FVA.Spec.CAbi

/-! `toy.wasm` (`clang --target=wasm32 -O2` from `toy.c`): what each export returns. -/

namespace Examples.Toy

open FVA.Wasm FVA.Wasm.Exec

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` below `lo`, `hi` above `hi`, else `x`. -/
def clamp : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
    [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)]

/-- `gcd(a, b)` on unsigned 32-bit ints: their greatest common divisor (`gcd(a, 0) = a`). -/
def gcd : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "gcd" [.i32 a, .i32 b]
    [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

/-- `sum_to(n)` on unsigned 32-bit ints: `0 + 1 + … + (n − 1)`, wrapped to 32 bits. -/
def sumTo : Prop :=
  ∀ n : BitVec 32, Returns Lifted.module "sum_to" [.i32 n]
    [.i32 (BitVec.ofNat 32 (List.range n.toNat).sum)]

end Examples.Toy
