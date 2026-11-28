import FVA.Self.Spec
import FVA.Proof.Decode.Module
import FVA.Proof.Exec.Det
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Numerics.Arith
import FVA.Proof.Trust
import FVA.Proof.Cert.Sort
import FVA.Proof.Cert.Compile
import FVA.Proof.Valid.Validator
import FVA.Proof.Valid.Complete
import FVA.Proof.Valid.Corollary
import FVA.Proof.Lib.Witness
import FVA.Spec.Exec.System
import FVA.Lifted

/-! Proofs of the self package's claims, from the unit theorems. -/

namespace FVA.Self.Proof

open FVA.Self

theorem decodeSound : DecodeSound := fun _ _ h => FVA.Wasm.Decode.decode_sound h

theorem decodeComplete : DecodeComplete := fun _ _ h => FVA.Wasm.Decode.decode_complete h

theorem stepSound : StepSound := fun _ _ _ h => FVA.Wasm.Exec.Ref.step_sound h

theorem runSound : RunSound := fun _ _ _ _ h => FVA.Wasm.Exec.Ref.run_sound h

theorem runDetMust : RunDetMust := fun _ _ _ _ _ h hQ => FVA.Wasm.Exec.Ref.runDet_must h hQ

theorem instantiateSound : InstantiateSound := fun _ _ _ _ _ _ _ hm h =>
  FVA.Wasm.Exec.Ref.instantiate_sound hm h

open FVA.Wasm.Num in
/-- Both Wasm float formats are sane. -/
theorem sane_of_mem {F : FloatFormat} (h : F ∈ [f32fmt, f64fmt]) : F.Sane := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  exacts [f32fmt_sane, f64fmt_sane]

theorem faddSound : FaddSound := fun _ hF _ _ h₁ h₂ =>
  FVA.Wasm.Num.fadd_mem (sane_of_mem hF) h₁ h₂

theorem fmulSound : FmulSound := fun _ hF _ _ h₁ h₂ =>
  FVA.Wasm.Num.fmul_mem (sane_of_mem hF) h₁ h₂

theorem fdivSound : FdivSound := fun _ hF _ _ h₁ h₂ =>
  FVA.Wasm.Num.fdiv_mem (sane_of_mem hF) h₁ h₂

theorem verdictCorrect : VerdictCorrect := FVA.Trust.verdict_pass_iff

theorem certSortSound : CertSortSound := FVA.Cert.SortedPerm.check_sound

theorem certCompileSound : CertCompileSound := FVA.Cert.Compiled.check_sound

theorem validateSound : ValidateSound := fun _ h => FVA.Wasm.Valid.validate_sound h

theorem validateComplete : ValidateComplete := fun _ h => FVA.Wasm.Valid.validate_complete h

theorem neverStuck : NeverStuck := FVA.Wasm.Valid.neverStuck

/-! Input-domain witnesses (U37): small concrete inputs; `fva trust` checks each against its
claim's obligation. -/

section Witnesses

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- A configuration with nothing left to run. -/
private def doneC : Config := ⟨{}, ⟨[], {}⟩, []⟩

private theorem fpInputs : ∃ F, F ∈ [f32fmt, f64fmt] ∧ ∃ z₁ z₂ : FVal, z₁.WF F ∧ z₂.WF F :=
  ⟨f32fmt, by simp, .inf false, .inf false, trivial, trivial⟩

@[fva_witness DecodeSound] theorem decodeSound_domain : fva_obligation% DecodeSound :=
  ⟨Binary.preamble, {}, rfl⟩

@[fva_witness DecodeComplete] theorem decodeComplete_domain : fva_obligation% DecodeComplete :=
  ⟨Binary.preamble, {}, Decode.decode_sound rfl⟩

@[fva_witness StepSound] theorem stepSound_domain : fva_obligation% StepSound :=
  ⟨NoHost, { doneC with instrs := [.plain .nop] }, doneC, rfl⟩

@[fva_witness RunSound] theorem runSound_domain : fva_obligation% RunSound :=
  ⟨⟨NoHost, 1, doneC, doneC, rfl⟩, ⟨NoHost, 1, doneC, doneC, rfl⟩⟩

@[fva_witness RunDetMust] theorem runDetMust_domain : fva_obligation% RunDetMust :=
  ⟨NoHost, fun _ => True, 1, doneC, doneC, rfl, fun _ _ => trivial⟩

@[fva_witness InstantiateSound] theorem instantiateSound_domain :
    fva_obligation% InstantiateSound :=
  ⟨NoHost, 1, {}, {}, {}, [], {}, .nil, rfl⟩

@[fva_witness FaddSound] theorem faddSound_domain : fva_obligation% FaddSound := fpInputs

@[fva_witness FmulSound] theorem fmulSound_domain : fva_obligation% FmulSound := fpInputs

@[fva_witness FdivSound] theorem fdivSound_domain : fva_obligation% FdivSound := fpInputs

@[fva_witness VerdictCorrect] theorem verdictCorrect_domain : fva_obligation% VerdictCorrect :=
  ⟨default, trivial⟩

/-- Empty input and output: both empty integer lists. -/
@[fva_witness CertSortSound] theorem certSortSound_domain : fva_obligation% CertSortSound :=
  ⟨⟨0, 0⟩, ⟨0, 0⟩, by decide +kernel⟩

/-- `(x+1)` and a toy module computing it (the bytes of `FVATest/Certs/Compile/E1`). -/
@[fva_witness CertCompileSound] theorem certCompileSound_domain :
    fva_obligation% CertCompileSound :=
  ⟨⟨wasm_bytes% "28782b31290a", 6⟩,
    ⟨wasm_bytes% "0061736d0100000001060160017f017f03020100070501016600000a09010700200041016a0b",
      38⟩, by decide +kernel⟩

@[fva_witness ValidateSound] theorem validateSound_domain : fva_obligation% ValidateSound :=
  ⟨{}, rfl⟩

@[fva_witness ValidateComplete] theorem validateComplete_domain :
    fva_obligation% ValidateComplete :=
  ⟨{}, Valid.validate_sound rfl⟩

end Witnesses

end FVA.Self.Proof
