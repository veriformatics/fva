import FVA.Spec.Binary.Module
import FVA.Spec.Claims
import FVA.Spec.Exec.Instantiate
import FVA.Spec.Trust
import FVA.Spec.Valid.Soundness
import FVA.Impl.Decode
import FVA.Impl.Exec.Det
import FVA.Impl.Valid
import FVA.Impl.Numerics.Float
import FVA.Trust.Verdict
import FVA.Impl.Cert.Sort
import FVA.Impl.Cert.Compile

/-!
# FVA's guarantees about itself (the self package's claims)

Each claim relates a verified implementation (`FVA.Impl.*`, `FVA.Trust.verdict`: the subjects)
to the reviewed-once spec (`FVA.Spec.*`: the base). `fva trust` on this module is the gate's
self-verification check (contract U7 S1); the proofs live in `FVA.Self.Proof`.
-/

namespace FVA.Self

open FVA.Wasm FVA.Wasm.Binary FVA.Wasm.Exec FVA.Wasm.Num

/-- Every module the decoder returns is the one the binary grammar assigns the bytes. -/
def DecodeSound : Prop :=
  ∀ (b : List UInt8) (m : Module), Decode.decode (pack b) b.length = .ok m → ModuleB m b

/-- The decoder returns the module of every encoding in the supported profile. -/
def DecodeComplete : Prop :=
  ∀ (b : List UInt8) (m : Module), ModuleB m b → Decode.decode (pack b) b.length = .ok m

/-- Every step of the reference stepper is a step of the execution semantics. -/
def StepSound : Prop :=
  ∀ (H : HostSem) (c c' : Config), Ref.step c = some c' → Step H c c'

/-- A stepper run that stops reaches a final configuration through semantic steps. -/
def RunSound : Prop :=
  ∀ (H : HostSem) (n : Nat) (c c' : Config), Ref.run n c = some c' →
    Steps H c c' ∧ ∃ o, Final c' o

/-- A deterministic run's final states satisfy every postcondition they satisfy along all
executions (total correctness from one run). -/
def RunDetMust : Prop :=
  ∀ (H : HostSem) (Q : Outcome → Prop) (n : Nat) (c c' : Config), Ref.runDet n c = some c' →
    (∀ o, Final c' o → Q o) → Must H Q c

/-- With matching imports, the instantiation the implementation computes is the spec's. -/
def InstantiateSound : Prop :=
  ∀ (H : HostSem) (fuel : Nat) (s s' : Store) (m : Module) (imports : List ExternVal)
    (inst : ModuleInst), ImportsMatch s m imports →
      Ref.instantiate fuel s m imports = some (s', inst) → Instantiated H m s imports s' inst

/-- Float addition (binary32 and binary64): the implementation's result is one the IEEE spec
allows. -/
def FaddSound : Prop :=
  ∀ F ∈ [f32fmt, f64fmt], ∀ z₁ z₂ : FVal, z₁.WF F → z₂.WF F → Impl.fadd F z₁ z₂ ∈ fadd F z₁ z₂

/-- Float multiplication (binary32 and binary64). -/
def FmulSound : Prop :=
  ∀ F ∈ [f32fmt, f64fmt], ∀ z₁ z₂ : FVal, z₁.WF F → z₂.WF F → Impl.fmul F z₁ z₂ ∈ fmul F z₁ z₂

/-- Float division (binary32 and binary64). -/
def FdivSound : Prop :=
  ∀ F ∈ [f32fmt, f64fmt], ∀ z₁ z₂ : FVal, z₁.WF F → z₂.WF F → Impl.fdiv F z₁ z₂ ∈ fdiv F z₁ z₂

/-- The trust verdict passes exactly when the reviewed verdict spec holds. -/
def VerdictCorrect : Prop :=
  ∀ r : FVA.Trust.Report, FVA.Trust.verdict r = .pass ↔ FVA.Trust.Pass r

/-- The sorted-integers certificate checker accepts only outputs in relation `SortedPerm`. -/
def CertSortSound : Prop :=
  ∀ i o : FVA.Cert.Blob, FVA.Cert.SortedPerm.check i o = true →
    FVA.Cert.Accepted FVA.Cert.SortedPerm i o

/-- The toy compiler's certificate checker accepts only outputs in relation `Compiled`. -/
def CertCompileSound : Prop :=
  ∀ i o : FVA.Cert.Blob, FVA.Cert.Compiled.check i o = true →
    FVA.Cert.Accepted FVA.Cert.Compiled i o

/-- The validator accepts only modules the typing rules make valid. -/
def ValidateSound : Prop :=
  ∀ m : Module, FVA.Wasm.Valid.validate m = true → FVA.Wasm.Valid.ModuleValid m

/-- Validated modules never get stuck: every configuration reachable from a well-typed call of an
export of a module the validator accepts is well typed and final or steps. -/
def NeverStuck : Prop := FVA.Wasm.Valid.NeverStuck FVA.Wasm.Valid.validate

end FVA.Self
