import FVATest.Certs.Sort.Py.Spec
import FVA.Proof.Cert.Sort

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Sort.Py

theorem claim_holds : claim :=
  FVA.Cert.SortedPerm.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Sort.Py
