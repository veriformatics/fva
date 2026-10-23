import FVA.Proof.Valid.InstantiateInvocation
import FVA.Proof.Valid.Instantiate
import FVA.Proof.Valid.Validator
import FVA.Proof.Valid.Soundness

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- Preservation iterated over a finite execution prefix. -/
theorem preservation_steps (pres : Preservation) {H : HostSem} (hh : TypeSoundHost H)
    {c c' : Config} {ts : List ValType} (hc : ConfigOK c ts) (steps : Steps H c c') :
    ConfigOK c' ts :=
  (InitProof.preservation_path pres hh hc steps).2

/-- The validator, initialization and runtime theorems compose at their stated boundaries. -/
theorem neverStuck_of (validate : Module → Bool)
    (sound : ∀ m, validate m = true → ModuleValid m)
    (pres : Preservation) (prog : Progress) (init : InstantiationOK) :
    NeverStuck validate := by
  intro H m s s' imports inst name a fi args c hv hh hs hi _ha hf hargs steps
  have hs' := (init H m s s' imports inst (sound m hv) hh hs hi).1
  have hc := preservation_steps pres hh (invocationOK s' a fi args hs' hf hargs) steps
  exact ⟨hc, prog H c fi.type.results hh.1 hc⟩

/-- The concrete validator's accepted artifacts inherit the runtime soundness theorems. -/
theorem validated_neverStuck (pres : Preservation) (prog : Progress) (init : InstantiationOK) :
    NeverStuck validate :=
  neverStuck_of validate (fun _ => validate_sound) pres prog init

/-- S1 and S2 suffice: the allocation bridge and invocation typing are already proved. -/
theorem neverStuck_of_typeSoundness (pres : Preservation) (prog : Progress) :
    NeverStuck validate :=
  validated_neverStuck pres prog (instantiationOK pres)

/-- The verified validator and runtime theorems discharge the complete never-stuck contract. -/
theorem neverStuck : NeverStuck validate :=
  neverStuck_of_typeSoundness preservation progress

end FVA.Wasm.Valid
