import FVA.Spec.Rel.Sort
import FVATest.Certs.Pos.Sorted.In
import FVATest.Certs.Pos.Sorted.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Pos.Sorted

/-- The bytes of
`FVATest/Certs/Pos/sorted-out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Neg/dup-in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Pos.Sorted
