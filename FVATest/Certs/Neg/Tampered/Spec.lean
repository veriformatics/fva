import FVA.Spec.Rel.Compile
import FVATest.Certs.Neg.Tampered.In
import FVATest.Certs.Neg.Tampered.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.Tampered

/-- The bytes of
`FVATest/Certs/Neg/e1-tampered.wasm`
stand in relation `FVA.Cert.Compiled` to the bytes of
`FVATest/Certs/Compile/e1.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.Compiled In.blob Out.blob

end FVATest.Certs.Neg.Tampered
