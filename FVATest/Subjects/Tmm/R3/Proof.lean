import FVATest.Subjects.Tmm.R3.Spec
import FVATest.Subjects.Tmm.Check

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Subjects.Tmm.R3

theorem claim_holds : claim :=
  Subjects.Tmm.FactorsDiffer.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Subjects.Tmm.R3
