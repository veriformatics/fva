import Toy.Def
import Toy.Proof

/-!
# `toy.wasm` specification — the human-review surface

Each theorem constrains the exported function of the compiled binary (`Toy.Lifted.module`,
lifted from sha256-pinned `toy.wasm`) for every input. Reviewers read these statements +
`Toy/Def.lean`; implementation (`toy.c`, compiler, `Toy/Lifted.lean`) + `Toy/Proof.lean` need
no review. `fva trust` computes this surface + audits axioms.
-/

namespace Toy
open FVA.Wasm

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` below `lo`, `hi` above `hi`, else `x`. -/
theorem clamp_spec (x lo hi : BitVec 32) :
    Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
      [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)] :=
  Proof.clamp_spec x lo hi

/-- `gcd(a, b)` on unsigned 32-bit ints terminates with the greatest common divisor. -/
theorem gcd_spec (a b : BitVec 32) :
    Returns Lifted.module "gcd" [.i32 a, .i32 b] [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))] :=
  Proof.gcd_spec a b

/-- `sum_to(n)` = `0 + 1 + … + (n - 1)` wrapped to 32 bits. -/
theorem sum_to_spec (n : BitVec 32) :
    Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))] :=
  Proof.sum_to_spec n

end Toy
