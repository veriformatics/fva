import Proofs.Model
import Proofs.Counts
import Proofs.Edge
import Proofs.Rna

namespace Proofs

/-- R1 at absolute tolerance 0.025: each of the seven shipped edgeR decimals
is within 1/40 of the real-arithmetic TMM factor defined in Model. The model uses
exact ranks with averaged ties, not floating-point ranks. This coarse tolerance
does not assert ten-place accuracy or verify the R implementation. -/
def r1 : Prop :=
  FVA.Cert.Accepted (Model.Accurate (1 / 40)) Counts.blob Edge.blob

/-- R2 at absolute tolerance 0.025: each of the seven shipped RNAnorm decimals
is within 1/40 of the real-arithmetic TMM factor defined in Model. The documented
defaults m_trim=0.3 and a_trim=0.05 are used. This coarse tolerance does not assert
ten-place accuracy or verify the Python implementation. -/
def r2 : Prop :=
  FVA.Cert.Accepted (Model.Accurate (1 / 40)) Counts.blob Rna.blob

/-- R3 fails for the shipped outputs: the seven corresponding factors do not
all agree even within an absolute error of 10^-10. -/
def r3_failure : Prop :=
  ¬ FVA.Cert.Accepted (Model.Agree (1 / 10^10)) Edge.blob Rna.blob

/-- Concrete R3 witness: the first shipped factors differ by more than 0.009,
and equal the stated exact decimal rationals. -/
def r3_witness : Prop :=
  (Model.factors Edge.blob.data)[0]? = some (99099942459293067 / 10^17 : ℚ) ∧
  (Model.factors Rna.blob.data)[0]? = some (9816880015656044 / 10^16 : ℚ) ∧
  |((Model.factors Edge.blob.data)[0]?.getD 0) -
    ((Model.factors Rna.blob.data)[0]?.getD 0)| > (9 / 1000 : ℚ)

end Proofs
