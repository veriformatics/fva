import Semantics
import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace SatAdd
-- The arithmetic-shift/XOR pair constructs the endpoint opposite the wrapped sign.
theorem mask (s : Word) : (s.sshiftRight 31 ^^^ (2147483648 : Word)).toInt =
    if s.toInt < 0 then 2147483647 else -2147483648 := by
  have hl := BitVec.le_toInt s
  have hu := BitVec.toInt_lt (x := s)
  change -2147483648 ≤ s.toInt at hl
  change s.toInt < 2147483648 at hu
  have hs : s.sshiftRight 31 = if s.toInt < 0 then (-1 : Word) else 0 := by
    apply BitVec.toInt_inj.mp
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    by_cases h : s.toInt < 0
    · simp only [h, ↓reduceIte]
      change s.toInt / 2147483648 = -1
      omega
    · simp only [h, ↓reduceIte]
      change s.toInt / 2147483648 = 0
      omega
  rw [hs]
  split <;> rfl

-- Signed interpretation of one wrapping i32 addition.
theorem wrapped (a b : Word) : (a+b).toInt =
    if a.toInt+b.toInt < -2147483648 then a.toInt+b.toInt+4294967296
    else if 2147483647 < a.toInt+b.toInt then a.toInt+b.toInt-4294967296
    else a.toInt+b.toInt := by
  have al := BitVec.le_toInt a
  have au := BitVec.toInt_lt (x := a)
  have bl := BitVec.le_toInt b
  have bu := BitVec.toInt_lt (x := b)
  change -2147483648 ≤ a.toInt at al
  change a.toInt < 2147483648 at au
  change -2147483648 ≤ b.toInt at bl
  change b.toInt < 2147483648 at bu
  rw [BitVec.toInt_add, Int.bmod_def]
  change (if (a.toInt+b.toInt) % 4294967296 < 2147483648 then
    (a.toInt+b.toInt) % 4294967296 else (a.toInt+b.toInt) % 4294967296 - 4294967296) = _
  split <;> split <;> (try split) <;> omega

-- A proof-only abbreviation; execution is connected to it by definitional reduction.
def result (a b : Word) : Word :=
  let s := a+b
  if (s.slt a) != (b.slt 0) then s.sshiftRight 31 ^^^ 2147483648 else s

-- Exhaust the sign/overflow cases with unbounded integer arithmetic.
theorem result_correct (a b : Word) : (result a b).toInt =
    if 2147483647 < a.toInt+b.toInt then 2147483647
    else if a.toInt+b.toInt < -2147483648 then -2147483648
    else a.toInt+b.toInt := by
  have hw := wrapped a b
  have hm := mask (a+b)
  have al := BitVec.le_toInt a
  have au := BitVec.toInt_lt (x := a)
  have bl := BitVec.le_toInt b
  have bu := BitVec.toInt_lt (x := b)
  change -2147483648 ≤ a.toInt at al
  change a.toInt < 2147483648 at au
  change -2147483648 ≤ b.toInt at bl
  change b.toInt < 2147483648 at bu
  unfold result
  by_cases ha : (a+b).toInt < a.toInt <;> by_cases hb : b.toInt < 0
  all_goals simp only [BitVec.slt, show (0 : Word).toInt = 0 from rfl,
    ha, hb, decide_true, decide_false, bne, ↓reduceIte, Bool.false_eq_true,
    Bool.not_false, Bool.not_true, Bool.false_beq, Bool.true_beq]
  all_goals first
    | rw [hm]; split <;> split at hw <;> (try split at hw) <;>
        split <;> (try split) <;> omega
    | split at hw <;> (try split at hw) <;> split <;> (try split) <;> omega
end SatAdd
