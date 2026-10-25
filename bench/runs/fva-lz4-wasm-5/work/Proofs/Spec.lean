import Proofs.Lifted
import Proofs.Format
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- The fresh allocation of the shipped module; callers modify only its memory. -/
noncomputable def allocation : Store × ModuleInst := allocModule {} Lifted.module [] [] []

/-- Observe exactly n bytes of memory 0, without changing it. -/
def bytesAt (s : Store) (p n : Nat) : Option (List UInt8) :=
  s.mems[0]?.map fun m => (List.range n).map fun j => m.byte (p + j)

/-- Thirteen input bytes: the first four-byte repeated sequence starts at index 4. -/
def encoderInput : List UInt8 := [0,1,2,3,65,65,65,65,65,66,67,68,69]

/-- The encoder's actual output: five literals, offset 1/match length 4, four literals. -/
def encoderOutput : List UInt8 := [80,0,1,2,3,65,1,0,64,66,67,68,69]

/-- Caller setup: grow memory by four pages; fill all 65,536 little-endian
hash words with -65536 (00 00 ff ff); write the input after the table.
Input [262144,262157) and output [300000,300029) do not overlap. -/
noncomputable def encoderStore : Store :=
  { allocation.1 with mems := allocation.1.mems.modify 0 fun m =>
      let grown := (m.grow 4).getD m
      { grown with byte := fun a =>
          if a < 262144 then (if a % 4 < 2 then 0 else 255)
          else if a < 262157 then encoderInput[a - 262144]! else grown.byte a } }

/-- A valid independent block: literal A, seven-byte match of offset 1,
then final literals B C D E F. The decoded result has length 13. -/
def validBlock : List UInt8 := [19,65,1,0,80,66,67,68,69,70]
def decodedBlock : List UInt8 := [65,65,65,65,65,65,65,65,66,67,68,69,70]

/-- Nonoverlapping decoder buffers: input [100,110), output [0,13). -/
noncomputable def decoderStore : Store := allocation.1.withBytes 100 validBlock

/-- The block is the single byte 00 at address 200. The next byte is caller
memory, outside the block; it is varied between 0 and 1. -/
noncomputable def emptyStore (next : UInt8) : Store := allocation.1.withBytes 200 [0,next,0]

/-- Identify an immediately executable unsigned byte load, skipping only canonical
i32 constants and descending into the active label/frame. The returned address
includes the instruction's static offset. No instruction is executed here. -/
def nextByteRead : Nat → List AInstr → Option Nat
  | 0, _ => none
  | _ + 1, .plain (.iconst .w32 base) :: .plain (.loadPacked .w32 .p8 .u m) :: _ =>
      if base < 2^32 then some (base + m.offset) else none
  | fuel + 1, .plain (.iconst .w32 base) :: es =>
      if base < 2^32 then nextByteRead fuel es else none
  | fuel + 1, .label _ _ body :: _ | fuel + 1, .frame _ _ body :: _ => nextByteRead fuel body
  | _, _ => none

/-- The named allocation is a real fresh instance under every host behavior,
and the module is instantiable. -/
def fresh_instance : Prop :=
  Instantiable Lifted.module ∧ ∀ H, Instance Lifted.module H allocation.1 allocation.2

/-- R1 fails: from the required hash-table setup, encoding these 13 bytes always
returns 13 and writes encoderOutput, which violates the supplied LZ4 end conditions. -/
def r1_counterexample : Prop :=
  (∀ H, CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144,.i32 13,.i32 300000]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 300000 13 = some encoderOutput)) ∧
  Format.decode encoderOutput = none

/-- R2 fails: validBlock decodes to decodedBlock in the format specification,
but the shipped decoder returns 1 and writes only its first literal A.
All buffers fit, are disjoint, and no memory growth is needed. -/
def r2_counterexample : Prop :=
  Format.decode validBlock = some decodedBlock ∧ decodedBlock.length = 13 ∧
  ∀ H, CallReturns H decoderStore allocation.2 "lz4BlockDecode"
    [.i32 100,.i32 10,.i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 13 = some (65 :: List.replicate 12 0))

/-- R3 fails even on the valid empty block 00: an execution reaches a byte load
at address 201, outside [200,201), and takes its next step. Additionally, varying
only that outside byte changes the call's return value from 0 to 4. -/
def r3_counterexample : Prop :=
  Format.decode [0] = some [] ∧
  (∀ H, ∃ c c', Steps H (invokeConfig (emptyStore 1) 3 [.i32 200,.i32 1,.i32 300]) c ∧
    nextByteRead 20 c.instrs = some 201 ∧ Step H c c') ∧
  (∀ H, CallReturns H (emptyStore 0) allocation.2 "lz4BlockDecode"
    [.i32 200,.i32 1,.i32 300] (fun _ vs => vs = [.i32 0])) ∧
  (∀ H, CallReturns H (emptyStore 1) allocation.2 "lz4BlockDecode"
    [.i32 200,.i32 1,.i32 300] (fun _ vs => vs = [.i32 4]))

end Proofs
