import FVATest.Subjects.Lz4Wasm.Lifted
import FVATest.Subjects.Lz4.Format
import FVA.Spec.CAbi

/-!
# What the shipped lz4-wasm codec does, against the LZ4 block format (claims; contract U14 S2)

Two machine-checked counterexamples to the task's requirements R1 and R3 (`bench/tasks/lz4-wasm`),
about the exact bytes of `lz4-block-codec.wasm` (the `Lifted` numeral, re-decoded by the kernel):

* `encode_not_valid` + `encode_returns`: on the 13-byte input `abaaaaaaaaaba`, prepared the way
  the interface describes (grow memory, fill the hash table with −65536, place the input),
  `lz4BlockEncode` returns a 12-byte block that is not a valid LZ4 block — its last match starts
  10 bytes before the end, and End-of-block condition 3 requires at least 12 (refuting R1).
* `decode_reads_past_input`: the valid empty block `00`, placed as the last byte of memory,
  makes `lz4BlockDecode` read past its one input byte, off the end of memory, and trap; a decoder
  obeying R3 (reads no byte outside the given block) returns 0 there instead (refuting R3).
-/

namespace Subjects.Lz4Wasm

open FVA.Wasm FVA.Wasm.Exec

/-- Addresses the interface fixes: the hash table at `getLinearMemoryOffset () = 0`, the input
right after it. -/
def inputAddr : Nat := 262144

/-- The 13-byte input `abaaaaaaaaaba`. -/
def encInput : List UInt8 :=
  [0x61, 0x62, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x61, 0x62, 0x61]

/-- The caller's preparation (interface README): grow memory 0 by 16 pages (1 → 17), fill the
65,536 four-byte hash-table words at address 0 with −65536 = `0xFFFF0000` (little-endian bytes
`00 00 FF FF`), write the input after the table. -/
def encPrep : List Prep :=
  [.grow 16, .fill 0 262144 (fun a => if a % 4 < 2 then 0 else 0xFF), .write inputAddr encInput]

/-- The 12-byte block `lz4BlockEncode` returns, at the output address `inputAddr + 13`. -/
def encBlock : List UInt8 :=
  [0x31, 0x61, 0x62, 0x61, 0x01, 0x00, 0x50, 0x61, 0x61, 0x61, 0x62, 0x61]

/-- R1 is false for the shipped encoder: from the prepared instance (grow, hash table = −65536,
input placed), `lz4BlockEncode inputAddr 13 (inputAddr + 13)` returns 12 and leaves `encBlock` at
the output address, yet `encBlock` is not a valid LZ4 block of any content — the only way it
parses is one match sequence whose literals end the block, and that fails End-of-block condition 3
(the last match starts 10 bytes before the end, not the required 12). R1 asks that every returned
block be valid. -/
def encode_breaks_r1 : Prop :=
  ReturnsOut Lifted.module encPrep "lz4BlockEncode" [.i32 (BitVec.ofNat 32 inputAddr), .i32 13,
      .i32 (BitVec.ofNat 32 (inputAddr + 13))] [.i32 12] (inputAddr + 13) encBlock ∧
    ∀ c, ¬ Lz4.Valid encBlock c

/-- The last address of the module's initial memory (1 page = 65536 bytes). -/
def lastByte : Nat := 65535

/-- R2 is false for the shipped decoder: the empty block `00` is a valid block (its content is
empty), yet, placed as the last byte of the initial memory, decoding it traps instead of returning
the content. The statement records the trap alone, not its cause. -/
def decode_traps_valid : Prop :=
  Lz4.Valid [0x00] [] ∧
    TrapsAfter Lifted.module [.write lastByte [0x00]] "lz4BlockDecode"
      [.i32 (BitVec.ofNat 32 lastByte), .i32 1, .i32 0]

end Subjects.Lz4Wasm
