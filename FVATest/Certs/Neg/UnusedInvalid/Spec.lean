import FVA.Spec.Rel.Compile
import FVATest.Certs.Neg.UnusedInvalid.In
import FVATest.Certs.Neg.UnusedInvalid.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.UnusedInvalid

/-- The bytes of
`FVATest/Certs/Neg/unused-invalid.wasm`
stand in relation `FVA.Cert.Compiled` to the bytes of
`FVATest/Certs/Neg/x.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.Compiled In.blob Out.blob

end FVATest.Certs.Neg.UnusedInvalid
