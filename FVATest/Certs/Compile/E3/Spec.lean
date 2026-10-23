import FVA.Spec.Rel.Compile
import FVATest.Certs.Compile.E3.In
import FVATest.Certs.Compile.E3.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Compile.E3

/-- The bytes of
`FVATest/Certs/Compile/e3.wasm`
stand in relation `FVA.Cert.Compiled` to the bytes of
`FVATest/Certs/Compile/e3.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.Compiled In.blob Out.blob

end FVATest.Certs.Compile.E3
