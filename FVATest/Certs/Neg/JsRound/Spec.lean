import FVA.Spec.Rel.Sort
import FVATest.Certs.Neg.JsRound.In
import FVATest.Certs.Neg.JsRound.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Certs.Neg.JsRound

/-- The bytes of
`FVATest/Certs/Neg/big-out-ts.txt`
stand in relation `FVA.Cert.SortedPerm` to the bytes of
`FVATest/Certs/Neg/big-in.txt`. -/
def claim : Prop := FVA.Cert.Accepted FVA.Cert.SortedPerm In.blob Out.blob

end FVATest.Certs.Neg.JsRound
