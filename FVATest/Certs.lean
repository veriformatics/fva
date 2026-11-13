import FVATest.Certs.Proof
-- a proof root of the mutation check (`FVATest/Mutate/config.json` `proofRoots`), outside the
-- test executables' closures: decoder mutants reach these rejection checks without re-keying
-- test-stage rows (`FVATest/DecodeDiag.lean`)
import FVATest.DecodeDiag
