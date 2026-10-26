import FVATest.Subjects.Tmm.Exact
import FVATest.Subjects.Tmm.EdgeR.In
import FVATest.Subjects.Tmm.EdgeR.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Subjects.Tmm.EdgeR

/-- The bytes of
`bench/tasks/tmm/edger-factors.txt`
stand in relation `Subjects.Tmm.RefutesExactAverageTMM` to the bytes of
`bench/tasks/tmm/counts.tsv`. -/
def claim : Prop := FVA.Cert.Accepted Subjects.Tmm.RefutesExactAverageTMM In.blob Out.blob

end FVATest.Subjects.Tmm.EdgeR
