import AvgFloor.Requirements

/-! Proven findings, NOT a replacement for the original requirements.
The default FVA audit checks these claims, including the refutations of R1 and R2.
Review this file, Requirements.lean, and Def.lean; no proof-module imports here. -/
namespace AvgFloor
open FVA.Wasm

/-- All inputs terminate without trapping, with a wrapped sum shifted right arithmetically. -/
def machine_behavior : Prop :=
  ∀ a b : BitVec 32, Returns Lifted.module "avg_floor" [.i32 a, .i32 b]
    [.i32 ((a + b).sshiftRight 1)]

/-- This characterizes every possible i32 result, not just one successful execution. -/
def exact_result : Prop :=
  ∀ a b r : BitVec 32,
    Returns Lifted.module "avg_floor" [.i32 a, .i32 b] [.i32 r] ↔
    r.toInt = wrappedMean a b

/-- The README's required answer is returned if and only if the sum does not overflow. -/
def correct_iff_sum_fits : Prop :=
  ∀ a b : BitVec 32,
    (∃ r : BitVec 32, Returns Lifted.module "avg_floor" [.i32 a, .i32 b] [.i32 r] ∧
      r.toInt = floorMean a b) ↔ sumFits a b

/-- Positive overflow: MAX + MAX returns -1 instead of MAX. -/
def positive_overflow : Prop :=
  Returns Lifted.module "avg_floor" [.i32 2147483647#32, .i32 2147483647#32]
    [.i32 (BitVec.ofInt 32 (-1))] ∧
  floorMean 2147483647#32 2147483647#32 = 2147483647 ∧
  ¬ Returns Lifted.module "avg_floor" [.i32 2147483647#32, .i32 2147483647#32]
    [.i32 2147483647#32]

/-- Negative overflow: MIN + MIN returns 0 instead of MIN. -/
def negative_overflow : Prop :=
  Returns Lifted.module "avg_floor" [.i32 2147483648#32, .i32 2147483648#32]
    [.i32 0#32] ∧
  floorMean 2147483648#32 2147483648#32 = -2147483648 ∧
  ¬ Returns Lifted.module "avg_floor" [.i32 2147483648#32, .i32 2147483648#32]
    [.i32 2147483648#32]

/-- The unchanged shipped binary does NOT meet R1. -/
def r1_false : Prop := ¬ Requirements.R1

/-- The unchanged shipped binary does NOT meet R2. -/
def r2_false : Prop := ¬ Requirements.R2

end AvgFloor
