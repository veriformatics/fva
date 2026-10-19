import FVA.Wasm.Semantics
import Toy.Lifted
import Toy.Def

/-!
# `toy.wasm` specification — the human-review surface

Each claim constrains an exported function of the compiled binary (`Toy.Lifted.module`, lifted
from sha256-pinned `toy.wasm`) for every input. Reviewers read this file + `Toy/Def.lean`;
`toy.c`, the compiler, `Toy/Lifted.lean` + `Toy/Proof.lean` need no review. This file imports
reviewed modules alone, so no unreviewed macro or notation can change what it says.
-/

namespace Toy
open FVA.Wasm

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `lo` below `lo`, `hi` above `hi`, else `x`. -/
def clamp_spec : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi]
    [.i32 (if x.slt lo then lo else if hi.slt x then hi else x)]

/-- `gcd(a, b)` on unsigned 32-bit ints terminates with the greatest common divisor. -/
def gcd_spec : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "gcd" [.i32 a, .i32 b]
    [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

/-- `sum_to(n)` = `0 + 1 + … + (n - 1)` wrapped to 32 bits. -/
def sum_to_spec : Prop :=
  ∀ n : BitVec 32, Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))]

end Toy
