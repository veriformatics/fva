import FVA.Spec.Rel.Sort
import FVATest.Certs.Sort.R.In
import FVATest.Certs.Sort.R.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Sort.R

/-- The bytes of
`FVATest/Certs/Sort/out-r.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Sort/input.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Sort.R
