import FVA.Spec.Rel.Sort
import FVATest.Certs.Neg.Trailing.In
import FVATest.Certs.Neg.Trailing.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.Trailing

/-- The bytes of
`FVATest/Certs/Neg/trailing-out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Neg/trailing-in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Neg.Trailing
