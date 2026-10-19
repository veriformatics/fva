import Init.Data.Int.DivMod.Basic
import Artifact

namespace AvgFloor

-- Exact module envelope: header, (i32,i32)->i32 type, function 0,
-- memory, exports (including avg_floor -> function 0), code/body sizes,
-- and zero local declarations. Only this 64-byte module shape is accepted.
def envelope : List Nat :=
  [0,97,115,109,1,0,0,0,1,7,1,96,2,127,127,1,127,3,2,1,0,
   5,3,1,0,1,7,22,2,6,109,101,109,111,114,121,2,0,9,97,118,
   103,95,102,108,111,111,114,0,0,10,12,1,10,0]

-- Signed integer presentation of i32 values. Addition wraps to [-2^31,2^31).
-- Only shift count 1 is supported: i32.shr_s then equals floor division by 2.
-- Other encodings/counts/stacks fail closed. Every instruction byte is consumed.
def exec (a b : Int) : List Nat → List Int → Option Int
  | [11], [v] => some v
  | 32 :: 0 :: code, stack => exec a b code (a :: stack)
  | 32 :: 1 :: code, stack => exec a b code (b :: stack)
  | 65 :: 1 :: code, stack => exec a b code (1 :: stack)
  | 106 :: code, y :: x :: stack => exec a b code ((x + y).bmod 4294967296 :: stack)
  | 117 :: code, 1 :: x :: stack => exec a b code (x / 2 :: stack)
  | _, _ => none

def run (bytes : List Nat) (a b : Int) : Option Int :=
  if bytes.take 55 = envelope ∧ bytes.length = 64 then
    exec a b (bytes.drop 55) []
  else none

def signed32 (x : Int) : Prop := -2147483648 ≤ x ∧ x < 2147483648

def R1 : Prop := ∀ a b : Int, signed32 a → signed32 b →
  run artifact a b = some ((a + b) / 2)

def R2 : Prop := ∀ a b : Int, signed32 a → signed32 b →
  (a + b < -2147483648 ∨ 2147483648 ≤ a + b) →
  run artifact a b = some ((a + b) / 2)

end AvgFloor
