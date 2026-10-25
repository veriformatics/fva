import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- Fresh allocation of the exact decoded artifact. -/
noncomputable def allocation : Store × ModuleInst :=
  allocModule {} Lifted.module [] [] []

def memory0 (s : Store) : MemInst :=
  s.mems[0]?.getD { pages := 0, max := none, byte := fun _ => 0 }

/-- Read back exactly n bytes of exported memory 0. -/
def bytesAt (s : Store) (p n : Nat) : List UInt8 :=
  (List.range n).map fun k => (memory0 s).byte (p + k)

/-- Encoder input: ASCII abcdeabcdefgh (13 bytes). -/
def encodeInput : List UInt8 := [97,98,99,100,101,97,98,99,100,101,102,103,104]

/-- Actual encoder output: five literals, offset 5 / match length 4, four final literals.
It violates both the five-final-literals and twelve-bytes-before-end rules. -/
def badBlock : List UInt8 := [80,97,98,99,100,101,5,0,64,101,102,103,104]

/-- Grow the exported memory by four pages, initialize all 65,536 hash words to
-65536 (bytes 00 00 ff ff), and write the input immediately after the table.
Output at 262208 is disjoint from the table and input and has ample room. -/
noncomputable def encoderStore : Store :=
  let grown := ((memory0 allocation.1).grow 4).getD (memory0 allocation.1)
  let hashed := { grown with byte := fun a =>
    if a < 262144 then (if a % 4 < 2 then 0 else 255) else grown.byte a }
  { allocation.1 with mems := [hashed.withBytes 262144 encodeInput] }

/-- R1 counterexample: on the documented initialization, the shipped encoder returns
13 and writes badBlock, whose last sequence has only four literals. -/
def r1_counterexample : Prop :=
  ∀ H, CallReturns H encoderStore allocation.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262208]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262208 13 = badBlock)

/-- Valid independent block: one 'a', offset 1 / match length 11, then five literals
'bcdef'. Decoded content is twelve 'a' bytes followed by 'bcdef' (17 bytes).
The last match starts 16 bytes before the decoded end. -/
def validBlock : List UInt8 := [23,97,1,0,80,98,99,100,101,102]

/-- R2 counterexample: validBlock at 100, output at 0, disjoint buffers in fresh
memory. The decoder returns only 1, leaving just 'a', instead of 17 bytes. -/
def r2_counterexample : Prop :=
  ∀ H, CallReturns H (allocation.1.withBytes 100 validBlock) allocation.2
    "lz4BlockDecode" [.i32 100, .i32 10, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 17 = 97 :: List.replicate 16 0)

/-- R3 counterexample: the valid one-byte empty block [00] at 0 produces different
return values when only the out-of-block byte at 1 changes. All buffers fit;
output is at 1024. This proves dependence on bytes outside [0,1). -/
def r3_counterexample : Prop :=
  ∀ H,
    CallReturns H (allocation.1.withBytes 0 [0,0,0]) allocation.2
      "lz4BlockDecode" [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 0]) ∧
    CallReturns H (allocation.1.withBytes 0 [0,1,0]) allocation.2
      "lz4BlockDecode" [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 4])

/-- R2/R3 boundary witness: the valid empty block occupies the last byte of the
one-page exported memory. No output bytes are needed. Decoding traps. -/
def empty_boundary_traps : Prop :=
  ∀ H, CallTraps H (allocation.1.withBytes 65535 [0]) allocation.2
    "lz4BlockDecode" [.i32 65535, .i32 1, .i32 0] (fun _ => True)

/-- Allocation really is a fresh instance under every host behavior; growing its
memory by four pages succeeds and gives the five-page memory used above. -/
def initialization : Prop :=
  (∀ H, Instance Lifted.module H allocation.1 allocation.2) ∧
  ((memory0 allocation.1).grow 4).isSome = true ∧
  (memory0 encoderStore).pages = 5
end Proofs
