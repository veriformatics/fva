/-! Mathematical vocabulary, independent of the implementation. Review this file. -/
namespace AvgFloor

/-- Unbounded mathematical sum of two signed 32-bit inputs. -/
def signedSum (a b : BitVec 32) : Int := a.toInt + b.toInt

/-- Lean's `Int` division by positive 2 is floor division, including negative odd sums. -/
def floorMean (a b : BitVec 32) : Int := signedSum a b / 2

/-- The sum, not merely the average, is representable as a signed 32-bit integer. -/
def sumFits (a b : BitVec 32) : Prop :=
  -2147483648 ≤ signedSum a b ∧ signedSum a b ≤ 2147483647

/-- Actual result as an unbounded integer: wrap the sum to signed 32 bits before halving. -/
def wrappedMean (a b : BitVec 32) : Int :=
  let s := signedSum a b
  (if s < -2147483648 then s + 4294967296
   else if 2147483647 < s then s - 4294967296 else s) / 2

end AvgFloor
