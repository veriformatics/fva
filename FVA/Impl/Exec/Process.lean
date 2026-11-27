import FVA.Impl.Exec.Machine

/-!
# Processes on the machine: unique-step instantiation, one answered host call (U29b)

`instantiateU` = `instantiate` with the initialization code run by `runU false`: a success is a
uniqueness certificate (every step no choice point of `Step`, the relation `Instantiated` uses),
which launch canonicalization needs (`FVA.Proof.Wasi.Canonical`). `answerHost X` = the step
`sysRun` takes at a host call, for a driver that answers some calls itself (one call's random
bytes) and resumes `sysRun`.
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

/-- Instantiate as `instantiate` does, the initialization code run by `runU false`: `none` unless it
returns with no value and no step was a choice point. -/
def instantiateU (fuel : Nat) (s : MStore) (m : Module) (imports : List ExternVal) :
    Option (MStore × ModuleInst) := do
  let (gvals, trefs, erefs) ← Ref.initCandidates fuel s.abs m imports
  guard (Ref.initAgrees fuel s.abs m imports gvals trefs erefs)
  let (s₁, inst) := s.alloc m imports gvals trefs erefs
  match MState.runU false fuel
      { store := s₁, frame := ⟨[], inst⟩, stack := [], code := (initCode m).map .plain, ctl := [] }
  with
  | (m', false) => match m'.ending with
    | .returned [] => some (m'.store, m'.frame.inst)
    | _ => none
  | (_, true) => none

/-- The process after host `X` answers its pending host call: `none` when no host call is pending
or `X` leaves it unanswered. -/
def answerHost {St : Type} (X : St → Nat → MStore → List Val → Option (St × MStore × MHostOut))
    (x : St × MState) : Option (St × MState) := do
  let (id, k, rest) ← x.2.hostCall
  let (τ, ms, r) ← X x.1 id x.2.store (x.2.stack.take k).reverse
  pure (τ, x.2.hostResume ms r.out rest k)

end FVA.Wasm.Exec.Machine
