import Proofs.Certificates.C0
import Proofs.Certificates.C1
import Proofs.Certificates.C2
import Proofs.Certificates.C3
import Proofs.Certificates.C4
import Proofs.Certificates.C5
import Proofs.Certificates.C6
import Proofs.Certificates.C7
import Proofs.Certificates.C8
import Proofs.Certificates.C9
import Proofs.Certificates.C10
import Proofs.Certificates.C11
import Proofs.Certificates.C12
import Proofs.Certificates.C13
import Proofs.Certificates.C14
import Proofs.Certificates.C15
namespace Certificates
open Verification
theorem checked_cases : cases.all checks = true := by
  change (checks C0.testcase && (checks C1.testcase && (checks C2.testcase && (checks C3.testcase && (checks C4.testcase && (checks C5.testcase && (checks C6.testcase && (checks C7.testcase && (checks C8.testcase && (checks C9.testcase && (checks C10.testcase && (checks C11.testcase && (checks C12.testcase && (checks C13.testcase && (checks C14.testcase && (checks C15.testcase && true)))))))))))))))) = true
  simp only [C0.checked, C1.checked, C2.checked, C3.checked, C4.checked, C5.checked, C6.checked, C7.checked, C8.checked, C9.checked, C10.checked, C11.checked, C12.checked, C13.checked, C14.checked, C15.checked, Bool.and_self]
end Certificates
