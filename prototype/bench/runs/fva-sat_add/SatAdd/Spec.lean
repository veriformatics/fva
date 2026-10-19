import FVA.Wasm.Semantics
import SatAdd.Lifted

/-!
# Requirements for the shipped `sat_add.wasm`

`BitVec 32` ranges over every 32-bit input pattern; `toInt` interprets that
pattern as a signed two's-complement integer. The additions below are in
unbounded `Int`, not wrapping machine arithmetic. `Returns` asserts both
termination without a trap and the exact single returned i32 value.

This specification imports no proof code or custom syntax.
-/

namespace SatAdd
open FVA.Wasm

/-- R1: If the mathematical sum is representable in signed 32 bits, return it. -/
def r1 : Prop :=
  ∀ a b : BitVec 32,
    -2147483648 ≤ a.toInt + b.toInt →
    a.toInt + b.toInt ≤ 2147483647 →
    Returns Lifted.module "sat_add" [.i32 a, .i32 b]
      [.i32 (BitVec.ofInt 32 (a.toInt + b.toInt))]

/-- R2: If the mathematical sum is above INT32_MAX, return INT32_MAX. -/
def r2 : Prop :=
  ∀ a b : BitVec 32,
    2147483647 < a.toInt + b.toInt →
    Returns Lifted.module "sat_add" [.i32 a, .i32 b] [.i32 2147483647#32]

/-- R3: If the mathematical sum is below INT32_MIN, return INT32_MIN. -/
def r3 : Prop :=
  ∀ a b : BitVec 32,
    a.toInt + b.toInt < -2147483648 →
    Returns Lifted.module "sat_add" [.i32 a, .i32 b] [.i32 2147483648#32]

end SatAdd
