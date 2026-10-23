import FVA.Spec.Rel.Sort
import FVATest.Cheats.CertEditedOut.In
import FVATest.Cheats.CertEditedOut.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Cheats.CertEditedOut

/-- The bytes of
`FVATest/Cheats/CertEditedOut/out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Cheats/CertEditedOut/in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Cheats.CertEditedOut
