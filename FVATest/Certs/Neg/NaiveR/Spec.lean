import FVA.Spec.Rel.Sort
import FVATest.Certs.Neg.NaiveR.In
import FVATest.Certs.Neg.NaiveR.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.NaiveR

/-- The bytes of
`FVATest/Certs/Sort/out-naive-r.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Sort/input.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Neg.NaiveR
