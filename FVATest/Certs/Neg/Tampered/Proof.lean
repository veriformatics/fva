import FVATest.Certs.Neg.Tampered.Spec
import FVA.Proof.Cert.Compile

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Neg.Tampered

theorem claim_holds : claim :=
  FVA.Cert.Compiled.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Neg.Tampered
