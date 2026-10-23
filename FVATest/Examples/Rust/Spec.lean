import FVATest.Examples.Rust.Lifted
import FVA.Spec.CAbi

/-! `rust.wasm` (`rustc --target wasm32-unknown-unknown -O` from `lib.rs`): the toy C claims on a
second source language, over the same trusted base. -/

namespace Examples.Rust

open FVA.Wasm FVA.Wasm.Exec

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` below `lo`, `hi` above `hi`, else `x`. -/
def clamp : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
    [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)]

/-- `gcd(a, b)` on unsigned 32-bit ints: their greatest common divisor (`gcd(a, 0) = a`). -/
def gcd : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "gcd" [.i32 a, .i32 b]
    [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

end Examples.Rust
