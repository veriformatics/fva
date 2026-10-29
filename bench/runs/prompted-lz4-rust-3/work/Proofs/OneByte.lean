import Proofs.Wasm
import Proofs.Spec
import Mathlib.Tactic.IntervalCases
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Results

def singleMemory (b : Nat) (mem : Nat → Nat) : Nat → Nat :=
  fun a => if a == 131072 then b else mem a

-- Every single-byte input, every output pointer and capacity, arbitrary other memory.
theorem one_byte (b dst cap : Nat) (mem : Nat → Nat) (hb : b < 256) :
    (Wasm.run 300 (Wasm.initial 131072 dst 1 cap (singleMemory b mem))).map
      (fun (r,s) => (r, s.mem, s.events)) =
    some (if b < 16 then 0 else Wasm.word-1, singleMemory b mem,
          [⟨false, 131072, 1⟩]) := by
  interval_cases b <;> run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, _, rhs) := (← goal.getType).eq? | throwError "equality expected"
    goal.assign (← Lean.Meta.mkEqRefl rhs)

theorem one_byte_format (b : Nat) (hb : b < 256) :
    LZ4.decode [b] = if b < 16 then some ⟨[], [], 0, true⟩ else none := by
  interval_cases b <;> run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let some (_, _, rhs) := (← goal.getType).eq? | throwError "equality expected"
    goal.assign (← Lean.Meta.mkEqRefl rhs)

end Results
