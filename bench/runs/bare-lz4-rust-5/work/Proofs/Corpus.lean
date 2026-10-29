import Proofs.Cases

namespace Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

-- Compile and execute the same explicit predicate for the larger fixtures.
-- This is a checked computation, not a kernel theorem about all inputs.
def main : IO Unit := do
  let mut count := 0
  for c in cases do
    if !check c then throw <| IO.userError s!"FAIL: {c.name}"
    count := count + 1
  IO.println s!"PASS: {count} artifact executions, access traces, and sequence certificates"

-- Kernel-reduced concrete executions. No native_decide or added axiom.
theorem short_cases_checked : (cases.take 5).all check = true := by
  decide +kernel

end Verification

def main : IO Unit := Verification.main
