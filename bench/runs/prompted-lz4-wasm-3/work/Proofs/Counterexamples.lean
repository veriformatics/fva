import Proofs.Artifact
import Proofs.LZ4
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification

def input1 : List Nat := [97,98,99,100,97,98,99,100,49,50,51,52,53]
def block1 : List Nat := [64,97,98,99,100,4,0,80,49,50,51,52,53]
def block2 : List Nat := [19,97,1,0,80,1,2,3,4,5]
def decoded2 : List Nat := [97,97,97,97,97,97,97,97,1,2,3,4,5]
def placed (bytes : List Nat) (base : Nat) : Nat → Nat :=
  fun a => if base ≤ a then bytes[a-base]?.getD 0 else 0

def encoderMemory (a : Nat) : Nat :=
  if a < 262144 then (if a % 4 < 2 then 0 else 255) else placed input1 262144 a

def encodeResult : VM := run 2000 artifact (start artifact 2 [262144,13,262208] encoderMemory 327680)
def decodeResult : VM := run 400 artifact (start artifact 3 [1024,10,0] (placed block2 1024) 65536)
def boundaryResult : VM := run 100 artifact (start artifact 3 [65534,1,0] (byteAt (placed [0] 65534) 65535 17) 65536)
def output (s : VM) (base n : Nat) : List Nat := (List.range n).map (fun i => s.memory (base+i))

theorem R1_counterexample :
    encodeResult.halted = true ∧ encodeResult.trapped = false ∧
    encodeResult.stack = [13] ∧ output encodeResult 262208 13 = block1 ∧
    LZ4.decode block1 = none := by decide

theorem R2_counterexample :
    LZ4.Valid block2 decoded2 ∧ decoded2.length = 13 ∧
    decodeResult.halted = true ∧ decodeResult.trapped = false ∧
    decodeResult.stack = [1] ∧ output decodeResult 0 13 = [97,0,0,0,0,0,0,0,0,0,0,0,0] := by unfold LZ4.Valid; decide

theorem R3_counterexample :
    LZ4.Valid [0] [] ∧ boundaryResult.halted = true ∧ boundaryResult.trapped = true ∧
    boundaryResult.reads = [65536,65535,65534] := by unfold LZ4.Valid; decide
end Verification
