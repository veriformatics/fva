import Proofs.Artifact

namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def outputBytes (m : Memory) (dst n : Nat) : List Nat :=
  (List.range n).map (fun i => readByte m (dst + i))

def exampleMemory (input : List Nat) : Memory :=
  putBytes (putBytes [] 65536 initialData) 131072 input

-- A concrete execution claim checks termination, every recorded access,
-- the return length, and every returned byte. Extra destination writes within
-- capacity are permitted, exactly as in R1.
def decodes (input expected : List Nat) (capacity : Nat) : Bool :=
  match invoke decoderModule 2000 131072 262144 input.length capacity
      (exampleMemory input) with
  | none => false
  | some r =>
    r.value == expected.length &&
    outputBytes r.memory 262144 r.value == expected &&
    safeTrace 131072 262144 input.length capacity r.trace

def rejectsSafely (input : List Nat) (capacity : Nat) : Bool :=
  match invoke decoderModule 2000 131072 262144 input.length capacity
      (exampleMemory input) with
  | none => false
  | some r => 2147483648 ≤ r.value &&
    safeTrace 131072 262144 input.length capacity r.trace

theorem emptyBlock : decodes [0] [] 0 = true := by decide

theorem literalBlock : decodes [48, 65, 66, 67] [65, 66, 67] 3 = true := by decide

-- One literal 'A', a seven-byte match with offset one, then five literals.
-- The last match starts exactly twelve decoded bytes before the end.
theorem overlapBlock :
    decodes [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]
      [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70] 13 = true := by decide

theorem zeroOffsetBlock :
    decodes [19, 65, 0, 0, 80, 66, 67, 68, 69, 70]
      [65, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70] 13 = true := by decide

theorem invalidOffset :
    rejectsSafely [19, 65, 2, 0, 80, 66, 67, 68, 69, 70] 13 = true := by decide

theorem undersizedOutput :
    rejectsSafely [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 12 = true := by decide

theorem truncatedLength : rejectsSafely [240] 100 = true := by decide

theorem literalExtension :
    decodes ([240, 0] ++ List.replicate 15 42) (List.replicate 15 42) 15 = true := by decide

-- Unused low nibble in the last token is legal: it is not a match field.
theorem unusedFinalNibble : decodes [15] [] 1 = true := by decide

end Verification
