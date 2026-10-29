import Proofs.InitTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Execution

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

noncomputable def freshMem : MemInst :=
  { pages := 32, max := some 32,
    byte := (Option.getD (fresh.store.mems[0]?) (MemInst.mk 0 none (fun _ => 0))).byte }

noncomputable def freshStore : Store :=
  { allocation.1 with mems := [freshMem], datas := [⟨[]⟩] }

theorem fresh_store : fresh.store = freshStore := by kernel_rfl

theorem fresh_funcs : freshStore.funcs = allocation.1.funcs := rfl

theorem fresh_mem_eq : freshStore.mems[0]? = some freshMem := rfl

theorem fresh_mem_size : ∃ mem, freshStore.mems[0]? = some mem ∧ mem.size = 2097152 :=
  ⟨freshMem, rfl, rfl⟩

end Proofs.Execution
