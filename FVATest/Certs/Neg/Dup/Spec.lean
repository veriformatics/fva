import FVA.Spec.Rel.Sort
import FVATest.Certs.Neg.Dup.In
import FVATest.Certs.Neg.Dup.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.Dup

/-- The bytes of
`FVATest/Certs/Neg/dup-out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Neg/dup-in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Neg.Dup
