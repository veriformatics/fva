import Cheat.Lifted
import FVA

/-!
# Planted cheats — `fva trust` must reject every one

1. `Lifted.lean` hand-edited: `clamp` returns `x` unchanged, so the false `clamp_spec` "proves".
2. `gcd_spec` rests on an `axiom`, not a proof.
3. `sum_to_spec` is `sorry`.
4. `sumBelow` carries `@[implemented_by]` pointing at wrong code; `native_decide` then
   "proves" `sumBelow 10 = 0` by running the wrong code.
5. `gcd_terminates` sounds like a claim about the binary but never mentions it.
-/

namespace Cheat
open FVA.Wasm

def sumBelowWrong (_ : Nat) : Nat := 0

@[implemented_by sumBelowWrong]
def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

theorem clamp_spec (x lo hi : BitVec 32) :
    Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi] [.i32 x] :=
  returns_of_invoke rfl ⟨5, by wasm_sim [Lifted.clamp]⟩

axiom gcd_correct (a b : BitVec 32) :
    Returns Lifted.module "gcd" [.i32 a, .i32 b] [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))]

theorem gcd_spec (a b : BitVec 32) :
    Returns Lifted.module "gcd" [.i32 a, .i32 b] [.i32 (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat))] :=
  gcd_correct a b

theorem sum_to_spec (n : BitVec 32) :
    Returns Lifted.module "sum_to" [.i32 n] [.i32 (BitVec.ofNat 32 (sumBelow n.toNat))] := by
  sorry

theorem sumBelow_ten : sumBelow 10 = 0 := by native_decide

theorem gcd_terminates (_a _b : BitVec 32) : True := trivial

end Cheat
