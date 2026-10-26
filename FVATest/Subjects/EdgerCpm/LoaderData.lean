import FVATest.Subjects.EdgerCpm.LoaderSetup

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable def dataBytes : List UInt8 :=
  ((Lifted.module.datas[0]?).getD (⟨[], .passive⟩ : FVA.Wasm.Data)).init

theorem dataBytes_length : dataBytes.length = 20236 := by decide +kernel

end Subjects.EdgerCpm.Existence
