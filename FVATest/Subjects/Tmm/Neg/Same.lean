import FVATest.Subjects.Tmm.R3.In
import FVATest.Subjects.Tmm.Check
/-! E2: the R3 certificate's checker rejects a file paired with itself (no line differs), so this
proof must fail at the kernel. -/
open FVATest.Subjects.Tmm.R3 in
theorem Subjects.Tmm.Neg.same : FVA.Cert.Accepted Subjects.Tmm.FactorsDiffer In.blob In.blob :=
  Subjects.Tmm.FactorsDiffer.check_sound In.blob In.blob (by kernel_rfl)
