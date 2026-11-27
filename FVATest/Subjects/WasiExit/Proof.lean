import FVATest.Subjects.WasiExit.Spec
import FVA.Proof.Wasi.Exit

/-! Proof of the exit claim: the lifted module is U29a's minimal command `cmd`, whose exit theorem
(`cmd_exits_zero`: launch canonicalization, the machine run to `proc_exit`, the WASI host's
answer, `machineRun_sysMust`) transfers. -/

namespace Subjects.WasiExit

theorem module_eq : Lifted.module = FVA.Wasi.LaunchExample.cmd := rfl

theorem exitsZero_proof : exitsZero := by
  unfold exitsZero
  rw [module_eq]
  exact FVA.Wasi.LaunchExample.cmd_exits_zero

end Subjects.WasiExit
