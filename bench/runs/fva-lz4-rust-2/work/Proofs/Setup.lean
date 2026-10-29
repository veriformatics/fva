import Proofs.Spec
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Valid.Validator

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem module_valid_holds : module_valid :=
  FVA.Wasm.Valid.validate_sound (by kernel_rfl)

private noncomputable def bootResult : Store × ModuleInst :=
  (instantiate 2000 {} Lifted.module []).getD ({}, {})

private noncomputable def bootMemory : MemInst :=
  (bootResult.1.mems[0]?).getD { pages := 0, max := none, byte := fun _ => 0 }

private theorem boot_eq : instantiate 2000 {} Lifted.module [] =
    some (codeStore bootMemory, allocation.2) := by kernel_rfl

private theorem boot_pages : bootMemory.pages = 32 := by kernel_rfl

theorem fresh_runtime_store_holds : fresh_runtime_store := by
  intro H
  exact ⟨bootMemory, boot_pages, instantiate_sound (by exact List.Forall₂.nil) boot_eq⟩

theorem initializable_holds : initializable := by
  intro H
  obtain ⟨mem, _, hi⟩ := fresh_runtime_store_holds H
  exact ⟨codeStore mem, allocation.2, hi⟩

end Proofs
