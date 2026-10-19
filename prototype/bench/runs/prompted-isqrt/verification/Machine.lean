import Bytecode

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

open Wasm
namespace Verification

def boundary (n lo hi oldMid oldFlag : Nat) : Config :=
  .live 23 [lo,n,hi-lo,hi,oldMid,oldFlag] [] [23]

theorem steps_add (a b : Nat) (c : Config) :
    steps code (a+b) c = (steps code a c).bind (steps code b) := by
  induction a generalizing c with
  | zero => simp [steps]
  | succ a ih =>
    simp only [Nat.succ_add, steps]
    cases h : step code c <;> simp [ih]

theorem done_steps (k r : Nat) : steps code k (.done r) = some (.done r) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [steps, step.eq_def] using ih

theorem initialize_state (n : Nat) (hn : n < 2^32) :
    steps code 10 (.live 0 [n,0,0,0,0,0] [] []) =
      some (boundary n 0 65536 0 0) := by
  unfold boundary
  execute_bytecode
  rw [Nat.mod_eq_of_lt hn]

end Verification
