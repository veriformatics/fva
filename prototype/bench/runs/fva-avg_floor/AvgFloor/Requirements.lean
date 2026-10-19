import FVA.Wasm.Semantics
import AvgFloor.Lifted
import AvgFloor.Def

/-! Original README requirements. These are FALSE for the unchanged artifact.
They are kept separate from the proven findings in `AvgFloor.Spec`. -/
namespace AvgFloor.Requirements
open FVA.Wasm

/-- R1: every signed 32-bit pair terminates with the mathematical floor average. -/
def R1 : Prop :=
  ∀ a b : BitVec 32, ∃ r : BitVec 32,
    Returns Lifted.module "avg_floor" [.i32 a, .i32 b] [.i32 r] ∧
    r.toInt = floorMean a b

/-- R2: in particular, the floor average is correct even when the sum overflows. -/
def R2 : Prop :=
  ∀ a b : BitVec 32, ¬ sumFits a b → ∃ r : BitVec 32,
    Returns Lifted.module "avg_floor" [.i32 a, .i32 b] [.i32 r] ∧
    r.toInt = floorMean a b

end AvgFloor.Requirements
