import FVATest.Certs.Pos.Sorted.Spec
import FVA.Proof.Cert.Sort

/-! Certificate proof written by `fva certify`: the kernel evaluates the checker. -/

namespace FVATest.Certs.Pos.Sorted

theorem claim_holds : claim :=
  FVA.Cert.SortedPerm.check_sound In.blob Out.blob (by kernel_rfl)

end FVATest.Certs.Pos.Sorted
