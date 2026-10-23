import FVATest.Certs.Neg.JsRound.Spec
import FVA.Proof.Cert.Sort

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Neg.JsRound

theorem claim_holds : claim :=
  FVA.Cert.SortedPerm.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Neg.JsRound
