import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- The shipped module, instantiated without imports. -/
noncomputable def allocation : Store × ModuleInst := allocModule {} Lifted.module [] [] []

/-- Encoder witness: 13 ASCII bytes, with a four-byte repeat at position 8. -/
def encodeInput : List UInt8 := [97,98,99,100,101,102,103,104,97,98,99,100,120]

/-- Returned block: eight literals, offset 8, match length 4, one final literal.
It violates both the five-final-literals and the twelve-byte-last-match rules. -/
def encoded : List UInt8 := [128,97,98,99,100,101,102,103,104,8,0,16,120]

/-- Caller grows memory to five pages, initializes all 65536 hash words to
-65536 (little endian 00 00 ff ff), and places input immediately after them. -/
noncomputable def encoderStore : Store :=
  { allocation.1 with mems := [{ pages := 5, max := none, byte := fun a =>
      if a < 262144 then (if a % 4 < 2 then 0 else 255)
      else if a < 262157 then encodeInput[a - 262144]! else 0 }] }

/-- A valid independent block: one literal A, offset 1, seven-byte match,
then five literals BCDEF. It decodes to AAAAAAAABCDEF (13 bytes). -/
def validBlock : List UInt8 := [19,65,1,0,80,66,67,68,69,70]

/-- Fresh one-page memory after the caller writes the valid block at 100. -/
noncomputable def decoderStore : Store := allocation.1.withBytes 100 validBlock

/-- Bytes of exported memory 0 at a particular address. -/
def memoryBytes (s : Store) (p n : Nat) : List UInt8 :=
  match s.mems[0]? with
  | none => []
  | some m => (List.range n).map (fun k => m.byte (p + k))

/-- R1 counterexample on the shipped artifact: encoding the specified 13 bytes
returns 13 and writes exactly `encoded`, an invalid LZ4 block. -/
def r1_counterexample : Prop := ∀ H,
  CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 300000]
    (fun s vs => vs = [.i32 13] ∧ memoryBytes s 300000 13 = encoded)

/-- R2 counterexample on a valid 10-byte block in nonoverlapping buffers with
ample capacity: decoder returns 1 instead of 13 and writes only the first A. -/
def r2_counterexample : Prop := ∀ H,
  CallReturns H decoderStore allocation.2 "lz4BlockDecode"
    [.i32 100, .i32 10, .i32 32]
    (fun s vs => vs = [.i32 1] ∧ memoryBytes s 32 13 = [65,0,0,0,0,0,0,0,0,0,0,0,0])

/-- R3 counterexample: the valid empty block [00] at the last memory byte.
Decoder traps reading a nonexistent offset after the final zero-literal token.
Output 32 is in bounds and no decoded output is required. -/
def r3_counterexample : Prop := ∀ H,
  CallTraps H allocation.1 allocation.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 32] (fun _ => True)

end Proofs
