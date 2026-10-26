import FVATest.Subjects.Tmm.Rel
import FVATest.Subjects.Tmm.R3.In
import FVATest.Subjects.Tmm.R3.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Subjects.Tmm.R3

/-- The bytes of
`bench/tasks/tmm/rnanorm-factors.txt`
stand in relation `Subjects.Tmm.FactorsDiffer` to the bytes of
`bench/tasks/tmm/edger-factors.txt`. -/
def claim : Prop := FVA.Cert.Accepted Subjects.Tmm.FactorsDiffer In.blob Out.blob

end FVATest.Subjects.Tmm.R3
