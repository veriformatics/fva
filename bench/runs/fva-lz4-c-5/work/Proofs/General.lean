import Proofs.Proof
import FVA.Proof.Lib
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option linter.all false
namespace Proofs

theorem zero_size_run {H : HostSem} {s : Store} {inst : ModuleInst}
    (src dst cap : BitVec 32)
    (hf : s.funcs[2]? = some (.wasm decoderType inst Lifted.func2)) :
    Must H (fun | .returned s' vs => s' = s ∧ vs = [.i32 (-1)] | .trapped _ => False)
      (invokeConfig s 2 [.i32 src, .i32 dst, .i32 0, .i32 cap]) := by
  have hzero : ieqz (0 : BitVec 32) = 1 := by decide +kernel
  have hltzero : iltS (0 : BitVec 32) 0#32 = 0 := by decide +kernel
  have hne : ine (0 : BitVec 32) 1#32 = 1 := by decide +kernel
  have hone : (1 : BitVec 32) ≠ 0 := by decide +kernel
  unfold invokeConfig
  by_cases hs : src = 0
  · subst src
    wasm_run [hf, Lifted.func2, decoderType, hzero, hltzero, hne, hone]
    exact Must.done (o := .returned s [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  · have hz : ieqz src = 0 := (ieqz_eq_zero src).mpr hs
    by_cases hc : iltS cap 0#32 = 0
    · by_cases hcap : cap = 0
      · subst cap
        wasm_run [hf, Lifted.func2, decoderType, hzero, hltzero, hne, hone, hz, hc]
        exact Must.done (o := .returned s [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      · wasm_run [hf, Lifted.func2, decoderType, hzero, hltzero, hne, hone, hz, hc, hcap]
        exact Must.done (o := .returned s [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    · wasm_run [hf, Lifted.func2, decoderType, hzero, hltzero, hne, hone, hz, hc]
      exact Must.done (o := .returned s [.i32 (-1)]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
theorem zero_size_general_holds : zero_size_general := by
  refine ⟨?_, ?_⟩
  · intro H; exact ⟨canonical.1, canonical.2, canonical_instance H⟩
  · intro src dst capacity H s inst hi
    have hu := instance_unique hi
    rw [hu.1, hu.2]
    refine ⟨2, by kernel_rfl, ?_, ?_⟩
    · refine ⟨_, canonical_func, ?_⟩
      simp [decoderType, Val.HasType, FuncInst.type]
    · exact zero_size_run src dst capacity canonical_func
end Proofs
