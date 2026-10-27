import Proofs.Model
import Proofs.Counts
import Proofs.Edger
import Proofs.RNAnorm

namespace Proofs

/-- R1 fails at absolute tolerance 10^-10 for exact default TMM with average
ranks: at least one of samples 3 and 4 is wrong, for every common normalizer.
This does not assert an error in reproducing edgeR's floating-point execution. -/
def R1_failure : Prop :=
  FVA.Cert.Accepted TMM.RejectsDefaultTMM Counts.blob Edger.blob

/-- R2 fails at absolute tolerance 10^-10 for exact default TMM with average
ranks: at least one of samples 3 and 4 is wrong, for every common normalizer.
This does not assert an error in reproducing RNAnorm's floating-point execution. -/
def R2_failure : Prop :=
  FVA.Cert.Accepted TMM.RejectsDefaultTMM Counts.blob RNAnorm.blob

/-- R3 fails: on the supplied matrix, the byte-exact files' first factors
have an absolute difference greater than 10^-10. -/
def R3_failure : Prop :=
  FVA.Cert.Accepted TMM.Disagree Edger.blob RNAnorm.blob

end Proofs
