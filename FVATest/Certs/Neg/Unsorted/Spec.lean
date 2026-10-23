import FVA.Spec.Rel.Sort
import FVATest.Certs.Neg.Unsorted.In
import FVATest.Certs.Neg.Unsorted.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.Unsorted

/-- The bytes of
`FVATest/Certs/Neg/unsorted-out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Neg/dup-in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Neg.Unsorted
