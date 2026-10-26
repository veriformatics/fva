import FVATest.Subjects.EdgerCpm.LoaderValues
import FVATest.Subjects.EdgerCpm.BulkInit
import FVATest.Subjects.EdgerCpm.LoaderPacking

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def initConfig : Config :=
  ⟨allocation.1, ⟨[], allocation.2⟩, (initCode Lifted.module).map .plain⟩

theorem initPrefix_some : (walk 22 initConfig).isSome := by decide +kernel
noncomputable def initPrefix : Config := (walk 22 initConfig).get initPrefix_some

theorem initPrefix_eq : walk 22 initConfig = some initPrefix :=
  (Option.some_get initPrefix_some).symm

def initSuffix : List AInstr := [.plain (.dataDrop 0), .plain (.call 76)]

theorem initPrefix_instrs : initPrefix.instrs = initInstrs 0 0 20236 0 ++ initSuffix := by
  kernel_rfl

theorem initPrefix_mem : initPrefix.store.mems[0]? = some environmentMem := by kernel_rfl

theorem initPrefix_data : initPrefix.store.datas[0]? = some ⟨dataBytes⟩ := by kernel_rfl

theorem initPrefix_memMap : initPrefix.frame.inst.mems[0]? = some 0 := by decide +kernel

theorem initPrefix_dataMap : initPrefix.frame.inst.datas[0]? = some 0 := by decide +kernel

noncomputable def afterData : Config :=
  ⟨initPrefix.store.setMem 0 (environmentMem.fill 0 20236 dataByte),
    initPrefix.frame, initSuffix⟩

end Subjects.EdgerCpm.Existence
