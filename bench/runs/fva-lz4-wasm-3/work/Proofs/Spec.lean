import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- Allocation of the actual decoded module, without imports. -/
noncomputable def fresh : Store × ModuleInst := allocModule {} Lifted.module [] [] []

/-- Thirteen input bytes: ASCII `abcdXabcd1234`. -/
def encoderInput : List UInt8 := [97, 98, 99, 100, 88, 97, 98, 99, 100, 49, 50, 51, 52]

/-- Observed encoder output: five literals, offset 5 / match length 4, four final literals. -/
def encoderOutput : List UInt8 := [80, 97, 98, 99, 100, 88, 5, 0, 64, 49, 50, 51, 52]

/-- Caller grows memory by four pages, fills each of the first 65536 little-endian
words with -65536 (00 00 ff ff), then puts input immediately after the table. -/
noncomputable def encoderStore : Store :=
  { fresh.1 with mems := fresh.1.mems.map fun (m : MemInst) =>
      let grown := (m.grow 4).getD m
      { grown with byte := fun a =>
          if a < 262144 then (if a % 4 < 2 then 0 else 255) else grown.byte a } }
    |>.withBytes 262144 encoderInput

/-- Bytes in memory 0 at p, with missing memory distinguished from empty bytes. -/
def bytesAt (s : Store) (p n : Nat) : Option (List UInt8) :=
  s.mems[0]?.map fun m => (List.range n).map fun k => m.byte (p + k)

/-- R1 counterexample. A legitimate fresh instance and caller preparation encode
`abcdXabcd1234` to the exact 13 bytes in encoderOutput at disjoint address 262200.
This block violates the required five final literals and last-match distance 12:
its final literal count is 4 and its last match starts at decoded position 5 of 13.
This disproves R1's validity conjunct, irrespective of its round-trip conjunct. -/
def r1 : Prop :=
  (∀ H, Instance Lifted.module H fresh.1 fresh.2) ∧
  (∀ H, CallReturns H encoderStore fresh.2 "lz4BlockEncode"
    [.i32 262144, .i32 13, .i32 262200]
    (fun s vs => vs = [.i32 13] ∧ bytesAt s 262200 13 = some encoderOutput))

/-- A valid independent LZ4 block: literal A, offset 1 / match length 7,
then five final literals BCDEF. Decoded content is AAAAAAAABCDEF (13 bytes).
The last match starts at position 1, exactly 12 bytes before the end. -/
def validBlock : List UInt8 := [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]

/-- R2 counterexample. With disjoint input [100,110) and output at 0, decoding
validBlock returns 1 and writes only A, rather than the required 13 bytes.
Both buffers fit in the original one-page memory. -/
def r2 : Prop :=
  ∀ H, CallReturns H (fresh.1.withBytes 100 validBlock) fresh.2 "lz4BlockDecode"
    [.i32 100, .i32 10, .i32 0]
    (fun s vs => vs = [.i32 1] ∧ bytesAt s 0 13 = some (65 :: List.replicate 12 0))

/-- R3 counterexample. Both calls supply the SAME valid one-byte block 00 at
input 0, with n=1 and disjoint output 1024. Changing only byte 1, OUTSIDE that
block, changes the return from 0 to 4. Thus an outside byte is successfully read
and affects execution, even for a valid block. All addresses fit in memory. -/
def r3 : Prop :=
  (∀ H, CallReturns H (fresh.1.withBytes 0 [0, 0, 0]) fresh.2 "lz4BlockDecode"
    [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 0])) ∧
  (∀ H, CallReturns H (fresh.1.withBytes 0 [0, 1, 0]) fresh.2 "lz4BlockDecode"
    [.i32 0, .i32 1, .i32 1024] (fun _ vs => vs = [.i32 4]))

/-- Additional R2/R3 witness. The valid empty block 00 occupies the last byte
of memory, input [65535,65536), output 0. The decoder traps by attempting to load
the nonexistent offset at 65536, instead of returning the required length 0. -/
def emptyBlockTrap : Prop :=
  ∀ H, CallTraps H (fresh.1.withBytes 65535 [0]) fresh.2 "lz4BlockDecode"
    [.i32 65535, .i32 1, .i32 0] (fun _ => True)

end Proofs
