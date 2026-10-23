import FVA.Spec.Valid.Runtime
import FVA.Spec.Claims
import FVA.Spec.Exec.Instantiate

/-!
# Type soundness statements (contract U6 S1–S4)

Proven in `FVA.Proof.Valid` (`preservation`, `progress`, `instantiationOK`, `invocationOK`,
`neverStuck`); `NeverStuck validate` is a self claim. Type soundness proves neither termination
nor the absence of specified traps.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- S1 Preservation: a step from a well-typed configuration extends the store and keeps the
configuration's type. -/
def Preservation : Prop :=
  ∀ (H : HostSem) (c c' : Config) (ts : List ValType), TypeSoundHost H → ConfigOK c ts →
    Step H c c' → Store.Extends c.store c'.store ∧ ConfigOK c' ts

/-- S2 Progress: a well-typed configuration is final or steps. -/
def Progress : Prop :=
  ∀ (H : HostSem) (c : Config) (ts : List ValType), ValidHost H → ConfigOK c ts →
    (∃ o, Final c o) ∨ ∃ c', Step H c c'

/-- S3 Instantiation: a valid module instantiated in a valid store gives a valid, extended
store and an instance typed by a context whose functions are the module's. -/
def InstantiationOK : Prop :=
  ∀ (H : HostSem) (m : Module) (s s' : Store) (imports : List ExternVal) (inst : ModuleInst),
    ModuleValid m → TypeSoundHost H → StoreOK s → Instantiated H m s imports s' inst →
      StoreOK s' ∧ Store.Extends s s' ∧ ∃ C, ModuleInstT s' inst C

/-- S3 Invocation: calling a function with arguments of its parameter types from a valid store
is a configuration of its result type. -/
def InvocationOK : Prop :=
  ∀ (s : Store) (a : Nat) (fi : FuncInst) (args : List Val), StoreOK s → s.funcs[a]? = some fi →
    List.Forall₂ (Val.HasType s) args fi.type.params →
      ConfigOK (invokeConfig s a args) fi.type.results

/-- S4 Validated modules never get stuck: every configuration reachable from a well-typed call
of an export of a module the validator accepts is well typed and final or steps. -/
def NeverStuck (validate : Module → Bool) : Prop :=
  ∀ (H : HostSem) (m : Module) (s s' : Store) (imports : List ExternVal) (inst : ModuleInst)
    (name : String) (a : Nat) (fi : FuncInst) (args : List Val) (c : Config),
    validate m = true → TypeSoundHost H → StoreOK s → Instantiated H m s imports s' inst →
      inst.exportFunc name = some a → s'.funcs[a]? = some fi →
      List.Forall₂ (Val.HasType s') args fi.type.params → Steps H (invokeConfig s' a args) c →
        ConfigOK c fi.type.results ∧ ((∃ o, Final c o) ∨ ∃ c', Step H c c')

end FVA.Wasm.Valid
