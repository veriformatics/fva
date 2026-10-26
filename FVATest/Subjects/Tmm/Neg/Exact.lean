import FVATest.Subjects.Tmm.EdgeR.In
import FVATest.Subjects.Tmm.Neg.ExactOut
import FVATest.Subjects.Tmm.ExactCheck
/-! E2: a factor file holding the exact average-rank TMM factors (12 decimals, from
`.scratch/u14/tmm/exact.py`) is no refutation, so the checker rejects it and this proof must fail at
the kernel. -/
open FVATest.Subjects.Tmm in
theorem Subjects.Tmm.Neg.exact : FVA.Cert.Accepted Subjects.Tmm.RefutesExactAverageTMM
    EdgeR.In.blob Neg.ExactOut.blob :=
  Subjects.Tmm.RefutesExactAverageTMM.check_sound EdgeR.In.blob Neg.ExactOut.blob (by kernel_rfl)
