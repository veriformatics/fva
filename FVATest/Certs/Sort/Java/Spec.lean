import FVA.Spec.Rel.Sort
import FVATest.Certs.Sort.Java.In
import FVATest.Certs.Sort.Java.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Sort.Java

/-- The bytes of
`FVATest/Certs/Sort/out-java.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Sort/input.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Sort.Java
