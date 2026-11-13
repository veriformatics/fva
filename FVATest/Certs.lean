import FVATest.Certs.Proof
-- a proof root of the mutation check (`FVATest/Mutate/config.json` `proofRoots`), outside the
-- test executables' closures: scope mutants reach these checks without re-keying test-stage rows
-- (`FVATest/DecodeDiag.lean`: decoder rejections; `FVATest/RuntimeDiag.lean`: instantiation's
-- tag index space + null tables)
import FVATest.DecodeDiag
import FVATest.RuntimeDiag
