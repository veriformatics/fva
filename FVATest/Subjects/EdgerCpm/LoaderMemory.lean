import FVATest.Subjects.EdgerCpm.LoaderPrefix

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

-- Elaborating the concrete store expands its data list; leave that reduction to the kernel.
attribute [local irreducible] initPrefix dataBytes dataByte

theorem initData_steps (H : HostSem) : Steps H initPrefix afterData := by
  change Steps H ⟨initPrefix.store, initPrefix.frame, initPrefix.instrs⟩ afterData
  rw [initPrefix_instrs]
  have h := steps_append (memory_init (H := H) (di := ⟨dataBytes⟩)
    initPrefix_memMap initPrefix_dataMap 20236 (s := initPrefix.store)
    (m := environmentMem) (d := 0) (q := 0) initPrefix_mem initPrefix_data
    (by rw [dataBytes_length]) (by decide) (by decide) (by decide)) initSuffix
  have he : (fun i => dataBytes[0 + i]!) = dataByte := by
    funext i
    simpa only [Nat.zero_add] using dataByte_eq i
  simpa only [afterData, he, List.nil_append] using h

end Subjects.EdgerCpm.Existence
