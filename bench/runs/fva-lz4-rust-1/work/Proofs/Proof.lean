import Proofs.Spec
import FVA.Proof.Lib
import Proofs.Execution
import Proofs.Samples

/-! Proofs: one theorem per claim, typed by the claim constant (`theorem answer_holds :
answer := …`). Nobody reads this file; `fva trust` checks it. -/

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem initializes_holds : initializes := by
  intro H
  exact ⟨Execution.freshStore, Execution.allocation.2, Execution.fresh_instance H⟩

theorem empty_call (H : HostSem) (s : Store) (inst : ModuleInst)
    (hf : s.funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩ inst Lifted.func7))
    (src dst cap : BitVec 32) :
    Must H (fun | .returned s' vs => s' = s ∧ vs = [.i32 4294967295]
                | .trapped _ => False)
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap]) := by
  unfold invokeConfig
  wasm_run [hf, Lifted.func7]
  exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

theorem empty_input_preserves_store_holds : empty_input_preserves_store := by
  refine ⟨initializes_holds, ?_⟩
  intro H s inst hi src dst cap p bytes
  obtain ⟨rfl, rfl⟩ := Execution.instance_unique hi
  have he : Execution.allocation.2.exportFunc "lz4_decompress" = some 7 := rfl
  have hf : (Execution.freshStore.withBytes p bytes).funcs[7]? = some (.wasm
      ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩
      Execution.allocation.2 Lifted.func7) := by
    rw [Store.withBytes_funcs, Execution.fresh_funcs]
    rfl
  refine ⟨7, he, ⟨_, hf, ?_⟩, empty_call H _ _ hf src dst cap⟩
  simp [Val.HasType, FuncInst.type]

theorem concrete_examples_holds : concrete_examples := by
  intro e he
  exact Samples.example_of_check e
    (List.all_eq_true.mp Samples.domains_checked e he)
    (List.all_eq_true.mp Samples.runs_checked e he)

end Proofs
