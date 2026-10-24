/-! Mutation-check fixture (U12 E1): nothing pins `pick`, so its mutants survive. -/

namespace Fix

/-- Unpinned: no theorem or test mentions it. -/
def pick (b : Bool) : Nat := bif b then 7 else 8

end Fix
