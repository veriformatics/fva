import FVATest.Subjects.Tmm.Exact
import FVATest.Subjects.Tmm.RNAnorm.In
import FVATest.Subjects.Tmm.RNAnorm.Out

/-! Certificate claim written by `fva certify`. -/

namespace FVATest.Subjects.Tmm.RNAnorm

/-- The bytes of
`bench/tasks/tmm/rnanorm-factors.txt`
stand in relation `Subjects.Tmm.RefutesExactAverageTMM` to the bytes of
`bench/tasks/tmm/counts.tsv`. -/
def claim : Prop := FVA.Cert.Accepted Subjects.Tmm.RefutesExactAverageTMM In.blob Out.blob

end FVATest.Subjects.Tmm.RNAnorm
