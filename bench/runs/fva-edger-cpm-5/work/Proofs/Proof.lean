import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem artifact_binding_holds : artifact_binding := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · rfl
  · rfl

private theorem cell_exec (c l out : Nat)
    (h : (runDet 40 (cellStart c l)).isSome = true)
    (hq : let f := (runDet 40 (cellStart c l)).get (by simpa using h)
          Final f (.returned f.store []) ∧ wrote out (.returned f.store [])) :
    ∀ H : HostSem, Must H (wrote out) (cellStart c l) := by
  intro H
  let f := (runDet 40 (cellStart c l)).get (by simpa using h)
  have hr : runDet 40 (cellStart c l) = some f := (Option.some_get _).symm
  exact runDet_must hr (by
    intro o ho
    have he : o = .returned f.store [] := by
      cases o with
      | returned s vs =>
        obtain ⟨hs, hi⟩ := ho
        have hv := vals_inj.mp (hq.1.2.symm.trans hi)
        cases hs; cases hv; rfl
      | trapped s => exact False.elim ((vals_ne_trap []) (hq.1.2.symm.trans ho.2))
    rw [he]; exact hq.2)

theorem r1_overflow_holds : r1_overflow := by
  refine ⟨artifact_binding_holds, cell_exec _ _ _ ?_ ?_⟩
  · decide +kernel
  · exact ⟨⟨rfl, rfl⟩, rfl, _, rfl, rfl⟩

theorem r2_boundary_holds : r2_boundary := by
  refine ⟨artifact_binding_holds, cell_exec _ _ _ ?_ ?_⟩
  · decide +kernel
  · exact ⟨⟨rfl, rfl⟩, rfl, _, rfl, rfl⟩

end Proofs
