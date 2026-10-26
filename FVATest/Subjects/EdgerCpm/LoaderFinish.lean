import FVATest.Subjects.EdgerCpm.Loader
import FVATest.Subjects.EdgerCpm.FiniteAllocator

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

attribute [local irreducible] initFinal allocation dataBytes dataByte

theorem runsExport_of_run {H : HostSem} {inst : ModuleInst} {name : String}
    {s : Store} {a n : Nat} {c : Config} (ha : inst.exportFunc name = some a)
    (h : run n (invokeConfig s a []) = some c)
    (hi : c.instrs = []) (hf : c.frame = ⟨[], {}⟩) :
    RunsExport H inst name s c.store := by
  simp only [RunsExport, ha]
  have hs := (run_sound (H := H) h).1
  have he : c = ⟨c.store, ⟨[], {}⟩, []⟩ := by rw [← hi, ← hf]
  rwa [he] at hs

theorem reloc_export : allocation.2.exportFunc "__wasm_apply_data_relocs" = some 75 := by
  decide +kernel

noncomputable def relocConfig : Config := invokeConfig initFinal.store 75 []

theorem relocFinal_some : (run 2000 relocConfig).isSome := by decide +kernel
noncomputable def relocFinal : Config := (run 2000 relocConfig).get relocFinal_some

theorem relocFinal_eq : run 2000 relocConfig = some relocFinal :=
  (Option.some_get relocFinal_some).symm

attribute [local irreducible] relocFinal

theorem relocFinal_instrs : relocFinal.instrs = [] := by kernel_rfl

theorem relocFinal_frame : relocFinal.frame = ⟨[], {}⟩ := by kernel_rfl

theorem relocated (H : HostSem) :
    RunsExport H allocation.2 "__wasm_apply_data_relocs" initFinal.store relocFinal.store :=
  runsExport_of_run reloc_export relocFinal_eq relocFinal_instrs relocFinal_frame

theorem ctors_export : allocation.2.exportFunc "__wasm_call_ctors" = some 74 := by decide +kernel

noncomputable def ctorsConfig : Config := invokeConfig relocFinal.store 74 []

theorem ctorsFinal_some : (run 2000 ctorsConfig).isSome := by decide +kernel
noncomputable def ctorsFinal : Config := (run 2000 ctorsConfig).get ctorsFinal_some

theorem ctorsFinal_eq : run 2000 ctorsConfig = some ctorsFinal :=
  (Option.some_get ctorsFinal_some).symm

attribute [local irreducible] ctorsFinal

theorem ctorsFinal_instrs : ctorsFinal.instrs = [] := by kernel_rfl

theorem ctorsFinal_frame : ctorsFinal.frame = ⟨[], {}⟩ := by kernel_rfl

theorem constructed (H : HostSem) :
    RunsExport H allocation.2 "__wasm_call_ctors" relocFinal.store ctorsFinal.store :=
  runsExport_of_run ctors_export ctorsFinal_eq ctorsFinal_instrs ctorsFinal_frame

theorem loader_ready (H : HostSem) :
    LoaderReady H Lifted.module env imports ctorsFinal.store allocation.2 :=
  ⟨initFinal.store, relocFinal.store, initialized H, relocated H, constructed H⟩

theorem loaded_mem_some : (ctorsFinal.store.mems[0]?).isSome := by decide +kernel
noncomputable def loadedMem : MemInst := (ctorsFinal.store.mems[0]?).get loaded_mem_some

theorem loaded_mem : ctorsFinal.store.mems[0]? = some loadedMem :=
  (Option.some_get loaded_mem_some).symm

theorem loaded_pages : loadedMem.pages = 49152 := by decide +kernel

theorem loaded_fits : FiniteAllocator.limit ≤ loadedMem.size := by
  change FiniteAllocator.limit ≤ loadedMem.pages * 65536
  rw [loaded_pages]
  decide

theorem loaded_linked : Linked ctorsFinal.store allocation.2 12 13 := by
  refine ⟨by decide +kernel, 160, 207, 12, 13, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl

end Subjects.EdgerCpm.Existence
