import FVATest.Subjects.Tmm.EdgeR.Spec
import FVATest.Subjects.Tmm.ExactCheck

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Subjects.Tmm.EdgeR

theorem claim_holds : claim :=
  Subjects.Tmm.RefutesExactAverageTMM.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Subjects.Tmm.EdgeR
