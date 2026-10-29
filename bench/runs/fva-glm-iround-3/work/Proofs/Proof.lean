import Proofs.Spec
import FVA.Proof.Lib
import Mathlib.Tactic.NormNum

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem r1_counterexample_holds : r1_counterexample := by
  have hx : ofBits f64fmt (0x3fdfffffffffffff : BitVec 64) =
      .normal false 4503599627370495 (-2) := by decide +kernel
  have hv : (ofBits f64fmt (0x3fdfffffffffffff : BitVec 64)).toReal f64fmt =
      (9007199254740991 : ℝ) / 18014398509481984 := by
    rw [hx]
    norm_num [FVal.toReal, f64fmt]
  unfold r1_counterexample
  dsimp only
  refine ⟨?_, hv, ?_, ?_, ?_, ?_⟩
  · rw [hx]; trivial
  · rw [hv]; norm_num
  · rw [hv]; norm_num
  · refine ⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩
    intro H s inst hi
    have ha := instance_alloc rfl rfl rfl rfl hi
    have hf : s.funcs[0]? = some (.wasm
        ⟨[.num .f64], [.num .i32]⟩ inst Lifted.func0) := by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
      rfl
    have he : inst.exportFunc "iround" = some 0 := by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
      rfl
    refine ⟨0, he, ⟨_, hf, by simp [Val.HasType, FuncInst.type]⟩, ?_⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    apply must_returned_of_runDet (n := 16)
      (s' := (allocModule {} Lifted.module [] [] []).1) (f' := ⟨[], {}⟩) (vs := [.i32 1])
    · kernel_rfl
    · rfl
  · rw [hv]; norm_num [abs_of_pos, abs_of_neg]

end Proofs
