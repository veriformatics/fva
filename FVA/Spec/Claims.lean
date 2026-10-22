import FVA.Spec.Exec.Step

/-!
# Claims about executions (reviewed spec)

The statement forms FVA proves about a module's executions. `Must` = total correctness: every
execution allowed by `Step` (every NaN choice, growth failure and host outcome) finishes, and
every finishing outcome satisfies the postcondition; a configuration with no successor that is
not finished, or an execution that runs forever, refutes it. `May` = some execution finishes so;
`PartialCorrect` = every finishing execution does. Outcomes carry the final store, so memory
effects are part of every postcondition; a trap is an outcome, so a total claim may allow one
explicitly. No claim mentions fuel.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- The outcome of a finished execution: values or a trap, with the final store. -/
inductive Outcome where
  | returned (s : Store) (vs : List Val)
  | trapped (s : Store)

/-- `c` has finished with outcome `o`: only values remain, or only `trap`. -/
def Final (c : Config) : Outcome → Prop
  | .returned s vs => c.store = s ∧ c.instrs = vals vs
  | .trapped s => c.store = s ∧ c.instrs = [.trap]

/-- Total correctness: from `c`, every execution finishes, with an outcome satisfying `Q`. -/
inductive Must (H : HostSem) (Q : Outcome → Prop) : Config → Prop where
  /-- `c` has finished with an outcome satisfying `Q`. -/
  | done {c o} : Final c o → Q o → Must H Q c
  /-- `c` can step, and every successor satisfies `Must`. -/
  | next {c} : (∃ c', Step H c c') → (∀ c', Step H c c' → Must H Q c') → Must H Q c

/-- Some execution from `c` finishes with an outcome satisfying `Q`. -/
def May (H : HostSem) (Q : Outcome → Prop) (c : Config) : Prop :=
  ∃ c' o, Steps H c c' ∧ Final c' o ∧ Q o

/-- Every execution from `c` that finishes has an outcome satisfying `Q`. -/
def PartialCorrect (H : HostSem) (Q : Outcome → Prop) (c : Config) : Prop :=
  ∀ c' o, Steps H c c' → Final c' o → Q o

/-- The configuration invoking function address `a` on `args` from outside (§4.5.5): an empty
frame, the arguments, `invoke a`. -/
def invokeConfig (s : Store) (a : Nat) (args : List Val) : Config :=
  ⟨s, ⟨[], {}⟩, vals args ++ [.invoke a]⟩

/-- The function address exported under `name`. -/
def ModuleInst.exportFunc (inst : ModuleInst) (name : String) : Option Nat :=
  inst.exports.findSome? fun e =>
    match e.value with
    | .func a => if e.name = name then some a else none
    | _ => none

/-- Calling export `name` of `inst` in store `s` on `args`: every execution finishes with an
outcome satisfying `Q`. -/
def CallMust (H : HostSem) (s : Store) (inst : ModuleInst) (name : String) (args : List Val)
    (Q : Outcome → Prop) : Prop :=
  ∃ a, inst.exportFunc name = some a ∧ Must H Q (invokeConfig s a args)

/-- The call always returns, with final store and results satisfying `P` (never traps). -/
def CallReturns (H : HostSem) (s : Store) (inst : ModuleInst) (name : String) (args : List Val)
    (P : Store → List Val → Prop) : Prop :=
  CallMust H s inst name args fun
    | .returned s' vs => P s' vs
    | .trapped _ => False

/-- The call always traps, with a final store satisfying `P`. -/
def CallTraps (H : HostSem) (s : Store) (inst : ModuleInst) (name : String) (args : List Val)
    (P : Store → Prop) : Prop :=
  CallMust H s inst name args fun
    | .returned _ _ => False
    | .trapped s' => P s'

/-- Some execution of the call finishes with an outcome satisfying `Q`. -/
def CallMay (H : HostSem) (s : Store) (inst : ModuleInst) (name : String) (args : List Val)
    (Q : Outcome → Prop) : Prop :=
  ∃ a, inst.exportFunc name = some a ∧ May H Q (invokeConfig s a args)

end FVA.Wasm.Exec
