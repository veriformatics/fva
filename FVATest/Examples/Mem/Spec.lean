import FVATest.Examples.Mem.Lifted
import FVA.Spec.CAbi

/-! `mem.wasm` (`clang --target=wasm32 -O2` from `mem.c`): what each export returns. -/

namespace Examples.Mem

open FVA.Wasm FVA.Wasm.Exec

/-- `array_sum(p, n)`: the sum, wrapped to 32 bits, of the `n` unsigned 32-bit words `xs` that
the caller wrote at address `p`, for every array inside the module's 64 KiB memory. -/
def arraySum : Prop :=
  ∀ (p : BitVec 32) (xs : List (BitVec 32)), p.toNat + 4 * xs.length ≤ 65536 →
    ReturnsAfterWrite Lifted.module p.toNat (le32s xs) "array_sum"
      [.i32 p, .i32 (BitVec.ofNat 32 xs.length)] [.i32 xs.sum]

/-- `call_scale(x)` on unsigned 32-bit ints: `(3x + 1) + (3(x + 1) + 1)`, wrapped to 32 bits. -/
def callScale : Prop :=
  ∀ x : BitVec 32, Returns Lifted.module "call_scale" [.i32 x]
    [.i32 (3 * x + 1 + (3 * (x + 1) + 1))]

/-- `classify(x, y)` on unsigned 32-bit ints, by the case `x`: `y + 7`, `y << 3`, `y xor 0x55`,
`100 y`, `y − 9` for `x` = 0 … 4 (wrapped to 32 bits), else 0. -/
def classify : Prop :=
  ∀ x y : BitVec 32, Returns Lifted.module "classify" [.i32 x, .i32 y]
    [.i32 (match x.toNat with
      | 0 => y + 7
      | 1 => y <<< 3
      | 2 => y ^^^ 0x55#32
      | 3 => y * 100
      | 4 => y - 9
      | _ => 0)]

end Examples.Mem
