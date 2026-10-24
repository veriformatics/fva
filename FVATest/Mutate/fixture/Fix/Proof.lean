import Fix.Clean
import Fix.Odd

/-! Mutation-check fixture (U12 E1): the theorems. -/

namespace Fix

theorem inc_two : inc 2 = 3 := rfl

/-- A changed `res` yields a planted resource diagnostic, as heartbeat exhaustion would. -/
theorem res_val : res = 5 := by
  first | decide | fail "maximum recursion depth has been reached"

end Fix
