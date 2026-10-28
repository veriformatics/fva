import Proofs.Cases

set_option Elab.async false

namespace Certificates

set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Kernel evaluation of exact return values, all byte access bounds, and the
    R2/R3 format/content obligations for the concrete cases in Cases.examples. -/
theorem checked_examples : Cases.examples.all Cases.conforms = true := by
  decide +kernel

#print axioms checked_examples

end Certificates
