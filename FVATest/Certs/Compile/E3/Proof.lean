import FVATest.Certs.Compile.E3.Spec
import FVA.Proof.Cert.Compile

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Compile.E3

theorem claim_holds : claim :=
  FVA.Cert.Compiled.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Compile.E3
