import FVATest.Certs.Custom.Rev.Spec
import FVATest.Certs.Custom.Check

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Custom.Rev

theorem claim_holds : claim :=
  FVATest.Certs.Custom.Reversed.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Custom.Rev
