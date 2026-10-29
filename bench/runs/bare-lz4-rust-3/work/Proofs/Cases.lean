import Proofs.Fixtures
namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

#eval do IO.println "Starting next certificate"; (← IO.getStdout).flush
theorem corpus_checks : certifiedCases.all checkCase = true := by decide_cbv

#eval do IO.println "Starting next certificate"; (← IO.getStdout).flush
theorem valid_format_checks : certifiedValidCases.all validReference = true := by decide_cbv

#eval do IO.println "Starting next certificate"; (← IO.getStdout).flush
theorem successful_reference_checks : (certifiedCases ++ certifiedTokens).all referenceAgrees = true := by decide_cbv

#eval do IO.println "Starting next certificate"; (← IO.getStdout).flush
theorem single_byte_checks : certifiedTokens.all checkCase = true := by decide_cbv

#print axioms empty_input
#print axioms corpus_checks
#print axioms valid_format_checks
#print axioms successful_reference_checks
#print axioms single_byte_checks

end Verification
