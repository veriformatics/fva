import FVATest.Examples.Mislabeled.Lifted
import FVA.Spec.CAbi

/-! `mislabeled.wasm` (`clang --target=wasm32 -O2` from `mislabeled.c`): what `clamp` returns. -/

namespace Examples.Mislabeled

open FVA.Wasm FVA.Wasm.Exec

/-- `clamp(x, lo, hi)` on signed 32-bit ints: `x` clamped into the range `[lo, hi]`. -/
def clamp : Prop :=
  ∀ x lo hi : BitVec 32, Returns Lifted.module "clamp" [.i32 x, .i32 lo, .i32 hi] [.i32 x]

end Examples.Mislabeled
