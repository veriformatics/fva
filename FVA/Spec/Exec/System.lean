import FVA.Spec.Claims

/-!
# Process executions (reviewed spec)

Claims about whole processes: a world state (files, streams, exit status) beside the Wasm
configuration, moved by host calls. `World.host σ τ` = the outcomes each host call may have from
world `σ`, leaving world `τ`. `SysStep` = one step of a process: a core step keeps the world, a
host call moves it, an exited process takes no step. `SysFinal` = how a process finished,
`SysMust` = every execution finishes with an outcome satisfying the postcondition. `fits` =
`StepP`'s growth policy (`true`: an embedder that grants every growth within the limits).

`proc_exit k` = a host outcome `trapped` (the post-call store) whose successor world records
`exited = some k`: the exit is final before the trap is, and the guest never resumes.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- The host relation of a module without host calls: no outcome. -/
def NoHost : HostSem := fun _ _ _ _ => False

/-- A world: its states, what each host call may do to it, and the exit a state records. -/
structure World where
  /-- World states (files, streams, process state). -/
  St : Type
  /-- `host σ τ`: the outcomes of each host call from world `σ` that leave world `τ`. -/
  host : St → St → HostSem
  /-- `some k` = the process ended with `proc_exit k`. -/
  exited : St → Option Nat
  /-- A call that never returns moves no world. -/
  stay : ∀ {σ τ : St} {id : Nat} {s : Store} {vs : List Val}, host σ τ id s vs .diverged → τ = σ

/-- One step of a process: a live process takes a step that a host-free rule explains, keeping
its world, or a host call that none explains, moving its world as the host allows. -/
def SysStep (W : World) (fits : Bool) : W.St × Config → W.St × Config → Prop
  | (σ, c), (τ, d) => W.exited σ = none ∧
    ((StepP NoHost fits c d ∧ τ = σ) ∨ (StepP (W.host σ τ) fits c d ∧ ¬ Step NoHost c d))

/-- How a process finished, with its final world and store: values returned, an explicit exit,
or abnormally (a trap). -/
inductive SysOutcome (St : Type) where
  | returned (σ : St) (s : Store) (vs : List Val)
  | exited (σ : St) (s : Store) (code : Nat)
  | abnormal (σ : St) (s : Store)

/-- Process state `x` has finished with outcome `o`; an exit recorded in the world comes first.
A command's `returned` from `_start` = exit 0. -/
def SysFinal (W : World) : W.St × Config → SysOutcome W.St → Prop
  | (σ, c), .returned σ' s vs => σ' = σ ∧ W.exited σ = none ∧ Final c (.returned s vs)
  | (σ, c), .exited σ' s k => σ' = σ ∧ W.exited σ = some k ∧ c.store = s
  | (σ, c), .abnormal σ' s => σ' = σ ∧ W.exited σ = none ∧ Final c (.trapped s)

/-- Total correctness of a process: every execution finishes, with an outcome satisfying `Q`. -/
inductive SysMust (W : World) (fits : Bool) (Q : SysOutcome W.St → Prop) :
    W.St × Config → Prop where
  /-- `x` has finished with an outcome satisfying `Q`. -/
  | done {x o} : SysFinal W x o → Q o → SysMust W fits Q x
  /-- `x` can step, and every successor satisfies `SysMust`. -/
  | next {x} : (∃ y, SysStep W fits x y) → (∀ y, SysStep W fits x y → SysMust W fits Q y) →
      SysMust W fits Q x

/-- `W` with the host outcomes environment `E` allows. -/
def World.restrict (W : World) (E : W.St → W.St → HostSem) : World where
  St := W.St
  host σ τ id s vs o := W.host σ τ id s vs o ∧ E σ τ id s vs o
  exited := W.exited
  stay h := W.stay h.1

/-- `E` keeps an outcome of every call `W` allows one for. -/
def Env.Total (W : World) (E : W.St → W.St → HostSem) : Prop :=
  ∀ σ id s vs, (∃ τ o, W.host σ τ id s vs o) → ∃ τ o, W.host σ τ id s vs o ∧ E σ τ id s vs o

end FVA.Wasm.Exec
