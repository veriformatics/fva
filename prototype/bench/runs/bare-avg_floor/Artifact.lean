import AvgFloor
import EmbedBytes

/-!
A deliberately restricted decoder and stack semantics for the instructions in
the shipped 64-byte WebAssembly module. This is not a general Wasm validator.
The fixed prefix checks the module version, types, function, memory, exports,
code-section length, function-body length, and empty local-declaration vector.
-/
namespace AvgFloor.Artifact

def expectedSource : String :=
  "/* Average of two 32-bit signed integers, rounded down. */\nint avg_floor(int a, int b) { return (a + b) >> 1; }\n"

def sourceSnapshot : String := include_str "avg_floor.c"

/-- Re-elaboration fails if the C file is changed. This pins the manual C model. -/
theorem source_matches : sourceSnapshot = expectedSource := by decide

def modulePrefix : List Nat := [
  0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, -- magic/version
  0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f, -- (i32,i32)->i32
  0x03, 0x02, 0x01, 0x00, -- one function, type 0
  0x05, 0x03, 0x01, 0x00, 0x01, -- one memory, minimum 1
  0x07, 0x16, 0x02, -- two exports
  0x06, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00, -- memory 0
  0x09, 0x61, 0x76, 0x67, 0x5f, 0x66, 0x6c, 0x6f, 0x6f, 0x72, 0x00, 0x00,
  0x0a, 0x0c, 0x01, 0x0a, 0x00 -- code section, one body, no locals
]

def bodyBytes : List Nat := [0x20, 0x01, 0x20, 0x00, 0x6a, 0x41, 0x01, 0x75, 0x0b]
def expectedBytes : List Nat := modulePrefix ++ bodyBytes

/-- Literal bytes read at elaboration, with no text decoding or generated axiom.
Main additionally checks the live file to guard against stale build caches. -/
def binarySnapshot : List Nat := include_bytes "avg_floor.wasm"

theorem binary_matches : binarySnapshot = expectedBytes := by decide
theorem module_length : expectedBytes.length = 64 := by decide
theorem prefix_length : modulePrefix.length = 55 := by decide

inductive Instruction where
  | localGet (index : Nat)
  | constOne
  | add
  | shrSigned
  deriving DecidableEq, Repr

/-- Only canonical encodings used by this module are accepted; `end` must be
last. Unsupported instructions/immediates and malformed input are rejected. -/
def decodeInstructions : List Nat → Option (List Instruction)
  | [0x0b] => some []
  | 0x20 :: i :: rest =>
      if i < 2 then (decodeInstructions rest).map (Instruction.localGet i :: ·) else none
  | 0x41 :: 0x01 :: rest => (decodeInstructions rest).map (Instruction.constOne :: ·)
  | 0x6a :: rest => (decodeInstructions rest).map (Instruction.add :: ·)
  | 0x75 :: rest => (decodeInstructions rest).map (Instruction.shrSigned :: ·)
  | _ => none

def decodeModule (bytes : List Nat) : Option (List Instruction) :=
  if bytes.length = 64 ∧ bytes.take 55 = modulePrefix then
    decodeInstructions (bytes.drop 55)
  else none

def program : List Instruction :=
  [.localGet 1, .localGet 0, .add, .constOne, .shrSigned]

theorem decode_binary : decodeModule binarySnapshot = some program := by decide

/-- Stack head is the top. Wasm shifts mask the count modulo the word width. -/
def step (locals : List I32) (stack : List I32) : Instruction → Option (List I32)
  | .localGet i => (locals[i]?).map (· :: stack)
  | .constOne => some (1 :: stack)
  | .add => match stack with
      | rhs :: lhs :: rest => some ((lhs + rhs) :: rest)
      | _ => none
  | .shrSigned => match stack with
      | rhs :: lhs :: rest => some (lhs.sshiftRight (rhs.toNat % 32) :: rest)
      | _ => none

def execute (locals : List I32) : List Instruction → List I32 → Option (List I32)
  | [], stack => some stack
  | instr :: rest, stack => do
      let stack' ← step locals stack instr
      execute locals rest stack'

def invoke (bytes : List Nat) (a b : I32) : Option I32 := do
  let instructions ← decodeModule bytes
  let stack ← execute [a, b] instructions []
  match stack with
  | [r] => some r
  | _ => none

theorem program_execution (a b : I32) :
    execute [a, b] program [] = some [wasmAvg a b] := by
  simp [execute, step, program, wasmAvg, BitVec.add_comm]

/-- Every input terminates without stack failure and returns the modeled word. -/
theorem artifact_execution (a b : I32) :
    invoke binarySnapshot a b = some (wasmAvg a b) := by
  simp [invoke, decode_binary, program_execution]

theorem artifact_correct_iff (a b : I32) :
    (invoke binarySnapshot a b).map BitVec.toInt = some (specification a b) ↔
      FitsI32 (a.toInt + b.toInt) := by
  simp only [artifact_execution, Option.map_some, Option.some.injEq]
  exact correct_iff_no_overflow a b

/-- The same result stated for the README's mathematical signed integers. -/
theorem artifact_correct_iff_integer_inputs (a b : Int)
    (ha : FitsI32 a) (hb : FitsI32 b) :
    (invoke binarySnapshot (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)).map BitVec.toInt =
      some ((a + b) / 2) ↔ FitsI32 (a + b) := by
  have h := artifact_correct_iff (BitVec.ofInt 32 a) (BitVec.ofInt 32 b)
  simpa only [specification, encoding_covers_signed_inputs a ha,
    encoding_covers_signed_inputs b hb] using h

/-- Counterexample directly for the embedded artifact, not just the formula. -/
theorem artifact_counterexample :
    (invoke binarySnapshot maxInput maxInput).map BitVec.toInt = some (-1) ∧
      specification maxInput maxInput = 2147483647 := by
  rw [artifact_execution]
  exact ⟨congrArg some max_counterexample.1, max_counterexample.2⟩

theorem artifact_violates_R1 :
    ¬ (∀ a b : I32,
      (invoke binarySnapshot a b).map BitVec.toInt = some (specification a b)) := by
  intro h
  have hc := h maxInput maxInput
  rw [artifact_counterexample.1, artifact_counterexample.2] at hc
  have hi : (-1 : Int) = 2147483647 := Option.some.inj hc
  omega

/-- Refutation of the overflowing-input part explicitly demanded by R2. -/
theorem artifact_violates_R2 :
    ¬ (∀ a b : I32, ¬ FitsI32 (a.toInt + b.toInt) →
      (invoke binarySnapshot a b).map BitVec.toInt = some (specification a b)) := by
  intro h
  have hc := h maxInput maxInput (by decide)
  rw [artifact_counterexample.1, artifact_counterexample.2] at hc
  have hi : (-1 : Int) = 2147483647 := Option.some.inj hc
  omega

end AvgFloor.Artifact
