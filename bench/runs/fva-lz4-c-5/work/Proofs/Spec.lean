import Proofs.Lifted
import Proofs.MemorySpec

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- A read of a finite byte string in exported memory 0. -/
def bytesAt (s : Store) (p n : Nat) : Option (List UInt8) :=
  s.mems[0]?.map fun m => (List.range n).map fun i => m.byte (p + i)

/-- Concrete calls start with the whole destination filled with 0xA5. -/
def prepared (s : Store) (src dst capacity : Nat) (input : List UInt8) : Store :=
  (s.withBytes dst (List.replicate capacity 165)).withBytes src input

def arguments (src dst size capacity : Nat) : List Val :=
  [.i32 (BitVec.ofNat 32 src), .i32 (BitVec.ofNat 32 dst),
   .i32 (BitVec.ofNat 32 size), .i32 (BitVec.ofNat 32 capacity)]

/-- Exact finite instances of R1 and of R2/R3's return-and-content conclusions.
These claims do not quantify over all compressed inputs. The export must return,
never trap, and obey the access restrictions at every intermediate state, under
every host behavior and from every fresh instance. -/
def CheckedCase (src dst : Nat) (input : List UInt8) (capacity : Nat)
    (result : BitVec 32) (output : List UInt8) : Prop :=
  131072 ≤ src ∧ src + input.length ≤ 2097152 ∧
  131072 ≤ dst ∧ dst + capacity ≤ 2097152 ∧
  (src + input.length ≤ dst ∨ dst + capacity ≤ src) ∧
  Instantiable Lifted.module ∧
  ∀ H s inst, Instance Lifted.module H s inst →
    Fits s src input.length ∧ Fits s dst capacity ∧
    CallReturns H (prepared s src dst capacity input) inst "LZ4_decompress_safe"
      (arguments src dst input.length capacity)
      (fun s' vs => vs = [.i32 result] ∧ bytesAt s' dst output.length = some output) ∧
    ∀ a, inst.exportFunc "LZ4_decompress_safe" = some a →
      Throughout H (fun c => accessesAllowed src dst input.length capacity c = true)
        (invokeConfig (prepared s src dst capacity input) a
          (arguments src dst input.length capacity))

/-- R1/R2/R3 boundary case: the canonical empty block with zero output capacity. -/
def empty_zero : Prop := CheckedCase 131072 262144 [0] 0 0 []

/-- R1/R2/R3 boundary case: the canonical empty block with positive capacity. -/
def empty_room : Prop := CheckedCase 131072 262144 [0] 1 0 []

/-- R1/R2/R3: a single literal, with exactly sufficient output capacity. -/
def one_literal : Prop := CheckedCase 131072 262144 [16, 97] 1 1 [97]

/-- R1/R2/R3: literal length 15 requires an extension byte of zero. -/
def extended_literals : Prop :=
  CheckedCase 131072 262144 ([240, 0] ++ List.replicate 15 97) 15 15 (List.replicate 15 97)

/-- R1/R2/R3: a match of offset 1 and length 7 overlaps its own output;
the last five bytes are literals, and the last match starts 12 bytes before EOF. -/
def overlap_match : Prop :=
  CheckedCase 131072 262144 [19, 97, 1, 0, 80, 98, 99, 100, 101, 102]
    13 13 (List.replicate 8 97 ++ [98, 99, 100, 101, 102])

/-- R1/R2/R3: match length 19 uses an extension byte of zero. -/
def extended_match : Prop :=
  CheckedCase 131072 262144 [31, 97, 1, 0, 0, 80, 98, 99, 100, 101, 102]
    25 25 (List.replicate 20 97 ++ [98, 99, 100, 101, 102])

/-- R1/R3's explicitly allowed offset-zero exception: existing destination bytes
are 0xA5, but all seven match bytes become zero. This is not an R2-valid block. -/
def zero_offset : Prop :=
  CheckedCase 131072 262144 [19, 97, 0, 0, 80, 98, 99, 100, 101, 102]
    13 13 ([97] ++ List.replicate 7 0 ++ [98, 99, 100, 101, 102])

/-- R1/R2/R3: source ends at the last byte of memory and output has exact capacity. -/
def source_at_end : Prop := CheckedCase 2097150 131072 [16, 97] 1 1 [97]

/-- R1/R2/R3: the decoded byte is written at the last byte of memory. -/
def destination_at_end : Prop := CheckedCase 131072 2097151 [16, 97] 1 1 [97]

/-- R1 malformed-input case: an empty compressed buffer is rejected as -1. -/
def reject_no_input : Prop := CheckedCase 131072 262144 [] 1 (-1) []

/-- R1 malformed-input case: a literal cannot fit in zero output capacity. -/
def reject_zero_capacity : Prop := CheckedCase 131072 262144 [16, 97] 0 (-1) []

/-- R1 malformed-input case: offset 2 after only one decoded literal is rejected.
No claim is made about the partially written output of this rejected call. -/
def reject_past_offset : Prop :=
  CheckedCase 131072 262144 [19, 97, 2, 0, 80, 98, 99, 100, 101, 102] 13 (-5) []
/-- For every 32-bit source pointer, destination pointer and capacity, zero
compressed bytes are rejected as -1, without any change to the store. This is a
universal boundary result, not a proof of R1/R2/R3 for nonempty blocks. -/
def zero_size_general : Prop :=
  Instantiable Lifted.module ∧
  ∀ (src dst capacity : BitVec 32) H s inst, Instance Lifted.module H s inst →
    CallReturns H s inst "LZ4_decompress_safe"
      [.i32 src, .i32 dst, .i32 0, .i32 capacity]
      (fun s' vs => s' = s ∧ vs = [.i32 (-1)])
end Proofs
