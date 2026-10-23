import FVATest.Certs.Custom.Rel
import FVATest.Certs.Custom.Rev.In
import FVATest.Certs.Custom.Rev.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Custom.Rev

/-- The bytes of
`FVATest/Certs/Custom/out.txt`
stand in relation `FVATest.Certs.Custom.Reversed` to the bytes of
`FVATest/Certs/Custom/in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVATest.Certs.Custom.Reversed In.blob Out.blob

end FVATest.Certs.Custom.Rev
