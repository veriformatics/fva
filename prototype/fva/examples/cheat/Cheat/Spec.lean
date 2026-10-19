import FVA.Wasm.Semantics
import Cheat.Lifted
import Cheat.Def
import Cheat.Syntax

/-!
# Planted cheats — `fva trust` must reject every one

1. `Lifted.lean` hand-edited: `clamp` returns `x` unchanged, so `clamp_spec` "proves".
2. `gcd_spec` rests on an `axiom` (`Cheat/Proof.lean`).
3. `sum_to_spec` is `sorry`.
4. `sum_to_zero` is proved from `1 = 2`, added with the kernel switched off.
5. `sumBelow_ten` "proves" `sumBelow 10 = 0` via `native_decide` over `implemented_by` code.
6. `gcd_terminates` sounds like a claim about the binary but never mentions it.
7. `sum_to_seven` reads as a claim about every input; `Cheat/Syntax.lean` makes it vacuous.
-/

namespace Cheat
open FVA.Wasm

def clamp_spec : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi] [.i32 x]

def gcd_spec : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "gcd" [.i32 a, .i32 b]
    [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

def sum_to_spec : Prop :=
  ∀ n : BitVec 32, Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))]

def sum_to_zero : Prop := ∀ n : BitVec 32, Returns Lifted.module "sum_to" [.i32 n] [.i32 0]

def sumBelow_ten : Prop := sumBelow 10 = 0

def gcd_terminates : Prop := ∀ _a _b : BitVec 32, True

def sum_to_seven : Prop := ∀ (n : BitVec 32), Returns Lifted.module "sum_to" [.i32 n] [.i32 7]

end Cheat
