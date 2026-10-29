import Proofs.InitRun
import FVA.Proof.Exec.Instantiate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Execution

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem config_eta (c : Config) : c = ⟨c.store, c.frame, c.instrs⟩ := rfl

theorem fresh_instance (H : HostSem) :
    Instance Lifted.module H freshStore allocation.2 := by
  refine ⟨by simp [ImportsMatch, Lifted.module], [.i32 65536], [], allocation.1,
    rfl, ?_, .nil, ?_⟩
  · exact .cons .refl .nil
  · have h := steps_of_walk (H := H) initial_walk
    have he : fresh = ⟨freshStore, ⟨[], allocation.2⟩, []⟩ := by
      calc
        fresh = ⟨fresh.store, fresh.frame, fresh.instrs⟩ := config_eta fresh
        _ = _ :=
          (congrArg (fun s => Config.mk s fresh.frame fresh.instrs) fresh_store).trans
            ((congrArg (fun f => Config.mk freshStore f fresh.instrs) fresh_frame).trans
              (congrArg (Config.mk freshStore ⟨[], allocation.2⟩) fresh_instrs))
    exact Eq.mp (congrArg (Steps H initial) he) h

end Proofs.Execution
