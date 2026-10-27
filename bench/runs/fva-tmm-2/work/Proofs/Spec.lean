import Proofs.Model
import Proofs.Counts
import Proofs.Edge
import Proofs.Rna

namespace Proofs

/-- R1, a conservative result: every edgeR artifact value is within absolute 0.023
of ideal TMM with exact average ranks. This is NOT a high-precision reproduction
of the floating-point implementation: see R1_tight_failure and VERIFICATION.md. -/
def R1 : Prop := FVA.Cert.Accepted (Model.Conforms (23 / 1000)) Counts.blob Edge.blob

/-- R2, a conservative result: every RNAnorm artifact value is within absolute 0.021
of ideal TMM with exact average ranks. The same floating-point caveat applies. -/
def R2 : Prop := FVA.Cert.Accepted (Model.Conforms (21 / 1000)) Counts.blob Rna.blob

/-- R3 FAILS: each of the seven pairs of shipped decimal values differs by more
than 1e-10, so agreement to ten decimal places is impossible. -/
def R3_failure : Prop := FVA.Cert.Accepted Model.Disagree Edge.blob Rna.blob

/-- Relative to the ideal-arithmetic model, sample 3 of edgeR's artifact is not
even within absolute 0.001. The coarse R1 tolerance must not be hidden. -/
def R1_tight_failure : Prop :=
  FVA.Cert.Accepted (Model.FailsTight (1 / 1000)) Counts.blob Edge.blob

/-- Relative to the ideal-arithmetic model, sample 3 of RNAnorm's artifact is not
even within absolute 0.001. This does not establish a defect in its libm execution. -/
def R2_tight_failure : Prop :=
  FVA.Cert.Accepted (Model.FailsTight (1 / 1000)) Counts.blob Rna.blob

end Proofs
