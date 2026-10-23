import FVA.Spec.Rel.Compile
import FVATest.Certs.Compile.E1.In
import FVATest.Certs.Compile.E1.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Compile.E1

/-- The bytes of
`FVATest/Certs/Compile/e1.wasm`
stand in relation `FVA.Cert.Compiled` to the bytes of
`FVATest/Certs/Compile/e1.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.Compiled In.blob Out.blob

end FVATest.Certs.Compile.E1
