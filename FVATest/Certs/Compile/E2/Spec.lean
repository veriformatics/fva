import FVA.Spec.Rel.Compile
import FVATest.Certs.Compile.E2.In
import FVATest.Certs.Compile.E2.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Compile.E2

/-- The bytes of
`FVATest/Certs/Compile/e2.wasm`
stand in relation `FVA.Cert.Compiled` to the bytes of
`FVATest/Certs/Compile/e2.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.Compiled In.blob Out.blob

end FVATest.Certs.Compile.E2
