import FVATest.Examples.Mislabeled.Spec
import FVA.Proof.Lib.Instance

/-! Proof of the mislabeled claim: proven, yet not what its name and docstring say. -/

namespace Examples.Mislabeled

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem clamp_holds : clamp := by
  intro x lo hi
  refine ⟨instantiable_alloc rfl rfl rfl rfl rfl rfl, ?_⟩
  intro H s inst h
  have ha := instance_alloc rfl rfl rfl rfl rfl h
  have hf : s.funcs[0]? = some (.wasm ⟨[⟨[.num .i32, .num .i32, .num .i32], [.num .i32]⟩],
      0⟩ inst Lifted.func0) := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  have he : inst.exportFunc "clamp" = some 0 := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha; rfl
  clear ha h
  refine ⟨0, he, ⟨_, _, hf, rfl, by simp [Val.HasType, FuncType.mapHeap, ValType.mapHeap]⟩, ?_⟩
  have hr : runDet 10 (invokeConfig s 0 [.i32 x, .i32 lo, .i32 hi]) =
      some ⟨s, ⟨[], {}⟩, vals [.i32 x]⟩ := by
    simp [runDet, wasm_step, invokeConfig, hf, Lifted.func0]
  exact must_returned_of_runDet hr rfl

end Examples.Mislabeled
