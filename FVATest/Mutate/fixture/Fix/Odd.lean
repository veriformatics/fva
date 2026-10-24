/-! Mutation-check fixture (U12 E1): outcomes that are neither kills nor survivals. -/

namespace Fix

/-- `Fix.res_val` fails with a resource diagnostic when `res` changes: inconclusive. -/
def res : Nat := 5

/-- The test hangs when `slow = 2` (timeout: inconclusive) and fails when `slow = 0`. -/
def slow : Nat := 1

/-- The test reports a crash (rc 3) when `crashy = 3`: inconclusive. -/
def crashy : Nat := 2

/-- The test reports an infrastructure failure (rc 2) when `infra = 5`: an error. -/
def infra : Nat := 4

/-- `FixTest`'s `#guard` fails when `panicky = 0` (a kill) and makes Lean panic without a
diagnostic when `panicky = 2` (`Nat.pow` exponent past a machine word: inconclusive). -/
def panicky : Nat := 1

end Fix
