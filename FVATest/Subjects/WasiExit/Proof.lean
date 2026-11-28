import FVATest.Subjects.WasiExit.Spec
import FVA.Proof.Wasi.Exit
import FVA.Proof.Lib.Witness

/-! Proof of the exit claim: the lifted module is U29a's minimal command `cmd`, whose exit theorem
(`cmd_exits_zero`: launch canonicalization, the machine run to `proc_exit`, the WASI host's
answer, `machineRun_sysMust`) transfers. -/

namespace Subjects.WasiExit

theorem module_eq : Lifted.module = FVA.Wasi.LaunchExample.cmd := rfl

theorem exitsZero_proof : exitsZero := by
  unfold exitsZero
  rw [module_eq]
  exact FVA.Wasi.LaunchExample.cmd_exits_zero

/-- The domain is inhabited (U37): a launch (the claim's first conjunct) and a live world. -/
@[fva_witness exitsZero] theorem exitsZero_domain : fva_obligation% exitsZero := by
  obtain ⟨c, mem, h⟩ := exitsZero_proof.1
  exact ⟨c, mem, h, FVA.Wasi.State.init [] [] [] [] [], rfl⟩

end Subjects.WasiExit
