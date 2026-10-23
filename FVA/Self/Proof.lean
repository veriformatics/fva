import FVA.Self.Spec
import FVA.Proof.Decode.Module
import FVA.Proof.Exec.Det
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Numerics.Arith
import FVA.Proof.Trust
import FVA.Proof.Cert.Sort
import FVA.Proof.Cert.Compile

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

end FVA.Self.Proof
