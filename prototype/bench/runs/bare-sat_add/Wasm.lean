import SatAdd

namespace SatAdd.Wasm

/-- Stack-free expression corresponding to the shipped optimized instruction sequence. -/
def optimized (a b : BitVec 32) : BitVec 32 :=
  let s := a + b
  let limit := s.sshiftRight 31 ^^^ 0x80000000#32
  if (b.slt 0#32 ^^ s.slt a) then limit else s

theorem wrapped_sum (a b : BitVec 32) :
    (a + b).toInt =
      if SatAdd.max32 < a.toInt + b.toInt then a.toInt + b.toInt - 4294967296
      else if a.toInt + b.toInt < SatAdd.min32 then a.toInt + b.toInt + 4294967296
      else a.toInt + b.toInt := by
  rw [BitVec.toInt_add]
  have h := SatAdd.sum_bounds a b
  simp only [SatAdd.min32, SatAdd.max32, show (2^32 : Nat) = 4294967296 from rfl,
    Int.bmod_def]
  by_cases hi : 2147483647 < a.toInt + b.toInt
  all_goals by_cases lo : a.toInt + b.toInt < -2147483648
  all_goals simp only [hi, lo, ite_true, ite_false]; split <;> omega

theorem overflow_test (a b : BitVec 32) :
    (b.slt 0#32 ^^ (a + b).slt a) =
      decide (SatAdd.max32 < a.toInt + b.toInt ∨ a.toInt + b.toInt < SatAdd.min32) := by
  have ha := SatAdd.input_bounds a
  have hb := SatAdd.input_bounds b
  rw [BitVec.slt, BitVec.slt, wrapped_sum]
  simp only [BitVec.toInt_zero, SatAdd.InInt32, SatAdd.min32, SatAdd.max32] at *
  by_cases hi : 2147483647 < a.toInt + b.toInt
  all_goals by_cases lo : a.toInt + b.toInt < -2147483648
  all_goals simp only [hi, lo, ite_true, ite_false]
  all_goals by_cases neg : b.toInt < 0
  all_goals simp [neg, Bool.xor]; omega

theorem shift_sign (s : BitVec 32) :
    s.sshiftRight 31 = if s.toInt < 0 then 0xffffffff#32 else 0#32 := by
  have hm := BitVec.msb_eq_toInt (x := s)
  have hall : 0xffffffff#32 = BitVec.allOnes 32 := by decide
  rw [hall]
  ext i
  rw [BitVec.getElem_sshiftRight]
  split
  · have : i = 0 := by omega
    subst i
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by decide : 31 < 32)] at hm
    rw [hm]
    split <;> simp_all only [decide_true, decide_false, BitVec.getElem_allOnes, BitVec.getElem_zero]
  · rw [hm]
    split <;> simp_all only [decide_true, decide_false, BitVec.getElem_allOnes, BitVec.getElem_zero]

theorem limit_value (s : BitVec 32) :
    s.sshiftRight 31 ^^^ 0x80000000#32 =
      if s.toInt < 0 then BitVec.ofInt 32 SatAdd.max32 else BitVec.ofInt 32 SatAdd.min32 := by
  rw [shift_sign]
  split <;> rfl

theorem optimized_correct (a b : BitVec 32) :
    (optimized a b).toInt = SatAdd.spec a.toInt b.toInt := by
  have hwrap := wrapped_sum a b
  have hsum := SatAdd.sum_bounds a b
  simp only [optimized]
  rw [overflow_test, limit_value]
  by_cases hi : SatAdd.max32 < a.toInt + b.toInt
  · have hn : (a + b).toInt < 0 := by
      simp only [hi, ite_true] at hwrap
      omega
    simp only [hi, true_or, decide_true, ite_true, hn]
    change (BitVec.ofInt 32 SatAdd.max32).toInt = _
    rw [SatAdd.narrowing_exact _ (by unfold SatAdd.InInt32 SatAdd.min32 SatAdd.max32; decide)]
    unfold SatAdd.spec
    simp only [SatAdd.min32, SatAdd.max32] at *
    omega
  · by_cases lo : a.toInt + b.toInt < SatAdd.min32
    · have hn : ¬ (a + b).toInt < 0 := by
        rw [ite_eq_right hi, ite_eq_left lo] at hwrap
        simp only [SatAdd.min32] at lo
        omega
      simp only [hi, lo, or_true, decide_true, ite_true, hn, ite_false]
      rw [SatAdd.narrowing_exact _ (by unfold SatAdd.InInt32 SatAdd.min32 SatAdd.max32; decide)]
      unfold SatAdd.spec
      simp only [SatAdd.min32, SatAdd.max32] at *
      omega
    · simp only [hi, lo, false_or, decide_false, Bool.false_eq_true, ite_false]
      rw [ite_eq_right hi, ite_eq_right lo] at hwrap
      rw [hwrap]
      unfold SatAdd.spec
      omega

theorem optimized_eq_c (a b : BitVec 32) : optimized a b = SatAdd.cSatAdd a b := by
  apply BitVec.eq_of_toInt_eq
  rw [optimized_correct, SatAdd.c_correct]

/-! A small, executable semantics for exactly the WebAssembly instructions used here.
The stack is top-first. All values are i32; local 2 starts at zero.
-/

inductive Instr where
  | localGet (index : Nat)
  | localTee (index : Nat)
  | i32Const (value : BitVec 32)
  | i32Add | i32ShrS | i32Xor | i32LtS | select
  deriving DecidableEq, Repr

def program : List Instr := [
  .localGet 0, .localGet 1, .i32Add, .localTee 2,
  .i32Const 31#32, .i32ShrS, .i32Const 0x80000000#32, .i32Xor,
  .localGet 2, .localGet 1, .i32Const 0#32, .i32LtS,
  .localGet 2, .localGet 0, .i32LtS, .i32Xor, .select]

structure State where
  locals : List (BitVec 32)
  stack : List (BitVec 32)
  deriving DecidableEq, Repr

def bool32 (b : Bool) : BitVec 32 := if b then 1#32 else 0#32

/-- Invalid stack or local accesses fail rather than silently assuming well-formedness. -/
def step (i : Instr) (s : State) : Option State :=
  match i, s.stack with
  | .localGet n, _ => do
      let x ← s.locals[n]?
      pure { s with stack := x :: s.stack }
  | .localTee n, x :: _ => do
      let _ ← s.locals[n]?
      pure { s with locals := s.locals.set n x }
  | .i32Const x, _ => some { s with stack := x :: s.stack }
  | .i32Add, y :: x :: rest => some { s with stack := (x + y) :: rest }
  | .i32ShrS, y :: x :: rest =>
      some { s with stack := x.sshiftRight (y.toNat % 32) :: rest }
  | .i32Xor, y :: x :: rest => some { s with stack := (x ^^^ y) :: rest }
  | .i32LtS, y :: x :: rest => some { s with stack := bool32 (x.slt y) :: rest }
  | .select, c :: y :: x :: rest =>
      some { s with stack := (if c ≠ 0#32 then x else y) :: rest }
  | _, _ => none

def run : List Instr → State → Option State
  | [], s => some s
  | i :: rest, s => (step i s).bind (run rest)

def invoke (code : List Instr) (a b : BitVec 32) : Option (BitVec 32) := do
  let s ← run code { locals := [a, b, 0#32], stack := [] }
  match s.stack with
  | [result] => some result
  | _ => none

theorem bool32_xor (a b : Bool) : bool32 a ^^^ bool32 b = bool32 (a ^^ b) := by
  cases a <;> cases b <;> decide

theorem bool32_ne_zero (b : Bool) : bool32 b ≠ 0#32 ↔ b = true := by
  cases b <;> decide

/-- Symbolic execution of every instruction; this also proves absence of traps. -/
theorem invoke_program (a b : BitVec 32) : invoke program a b = some (optimized a b) := by
  change some (if bool32 (b.slt 0#32) ^^^ bool32 ((a + b).slt a) ≠ 0#32 then
    (a + b).sshiftRight 31 ^^^ 0x80000000#32 else a + b) = some (optimized a b)
  simp only [bool32_xor, bool32_ne_zero]
  rfl

/-! Deliberately narrow decoder: it accepts only this module layout and the
instruction/immediate encodings used by this artifact. Unsupported input fails.
The metadata specifies one (i32,i32)->i32 function, one memory, exports
memory and sat_add (function 0), and one additional i32 local.
-/

def modulePrefix : List Nat := [
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
  0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f,
  0x03, 0x02, 0x01, 0x00,
  0x05, 0x03, 0x01, 0x00, 0x01,
  0x07, 0x14, 0x02, 0x06, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00,
  0x07, 0x73, 0x61, 0x74, 0x5f, 0x61, 0x64, 0x64, 0x00, 0x00,
  0x0a, 0x25, 0x01, 0x23, 0x01, 0x01, 0x7f]

def decodeInstructions : List Nat → Option (List Instr)
  | [0x0b] => some [] -- end; reject trailing bytes
  | 0x20 :: n :: rest =>
      if n < 128 then (.localGet n :: ·) <$> decodeInstructions rest else none
  | 0x22 :: n :: rest =>
      if n < 128 then (.localTee n :: ·) <$> decodeInstructions rest else none
  | 0x41 :: 0x00 :: rest => (.i32Const 0#32 :: ·) <$> decodeInstructions rest
  | 0x41 :: 0x1f :: rest => (.i32Const 31#32 :: ·) <$> decodeInstructions rest
  | 0x41 :: 0x80 :: 0x80 :: 0x80 :: 0x80 :: 0x78 :: rest =>
      (.i32Const 0x80000000#32 :: ·) <$> decodeInstructions rest
  | 0x6a :: rest => (.i32Add :: ·) <$> decodeInstructions rest
  | 0x75 :: rest => (.i32ShrS :: ·) <$> decodeInstructions rest
  | 0x73 :: rest => (.i32Xor :: ·) <$> decodeInstructions rest
  | 0x48 :: rest => (.i32LtS :: ·) <$> decodeInstructions rest
  | 0x1b :: rest => (.select :: ·) <$> decodeInstructions rest
  | _ => none

def decodeModule (bytes : List Nat) : Option (List Instr) :=
  if bytes.length = 87 ∧ bytes.take modulePrefix.length = modulePrefix then
    decodeInstructions (bytes.drop modulePrefix.length)
  else none

end SatAdd.Wasm
