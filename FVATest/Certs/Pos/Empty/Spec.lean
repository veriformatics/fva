import FVA.Spec.Rel.Sort
import FVATest.Certs.Pos.Empty.In
import FVATest.Certs.Pos.Empty.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Pos.Empty

/-- The bytes of
`FVATest/Certs/Pos/empty.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Pos/empty.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Pos.Empty
