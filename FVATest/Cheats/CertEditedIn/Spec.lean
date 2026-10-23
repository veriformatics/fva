import FVA.Spec.Rel.Sort
import FVATest.Cheats.CertEditedIn.In
import FVATest.Cheats.CertEditedIn.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Cheats.CertEditedIn

/-- The bytes of
`FVATest/Cheats/CertEditedIn/out.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Cheats/CertEditedIn/in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Cheats.CertEditedIn
