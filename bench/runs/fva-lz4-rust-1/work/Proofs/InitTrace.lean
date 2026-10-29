import Proofs.Lifted
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Valid.InstantiateConst

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Execution

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

noncomputable def allocation : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []

noncomputable def initial : Config :=
  ⟨allocation.1, ⟨[], allocation.2⟩, (initCode Lifted.module).map .plain⟩

noncomputable def fresh : Config := (walk 1418 initial).getD initial

theorem initial_walk : walk 1418 initial = some fresh := by kernel_rfl

theorem fresh_instrs : fresh.instrs = [] := by kernel_rfl

theorem fresh_frame : fresh.frame = ⟨[], allocation.2⟩ := by kernel_rfl

end Proofs.Execution
