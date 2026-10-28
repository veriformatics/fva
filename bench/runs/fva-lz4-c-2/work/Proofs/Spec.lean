import Proofs.Lifted
import FVA.Spec.CAbi

/-! Partial coverage of README R1–R3. These claims are explicitly restricted cases,
not formalizations of the three universal requirements. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- A concrete decode in every fresh instance, under every host semantics. The destination
is first filled with 0xA5. The call must terminate without a trap, return the expected
length, and produce every expected byte. The immediately adjacent destination bytes must
be preserved. Source = 131072, destination = 196608; capacity is in bytes. -/
def DecodeCase (input output : List UInt8) (capacity : Nat) : Prop :=
  (∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
    Fits s 131072 input.length ∧ Fits s 196607 (capacity + 2)) ∧
  ∀ H s inst, Instance Lifted.module H s inst →
    Fits s 131072 input.length → Fits s 196607 (capacity + 2) →
    CallReturns H
      ((s.withBytes 196608 (List.replicate capacity 165)).withBytes 131072 input)
      inst "LZ4_decompress_safe"
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]
      (fun s' vs => vs = [.i32 (BitVec.ofNat 32 output.length)] ∧
        ∃ before after, s.mems[0]? = some before ∧ s'.mems[0]? = some after ∧
          (∀ k : Fin output.length, after.byte (196608 + k.val) = output[k.val]) ∧
          after.byte 196607 = before.byte 196607 ∧
          after.byte (196608 + capacity) = before.byte (196608 + capacity))

/-- R2 boundary case: the empty block [0] with zero destination capacity. -/
def emptyBlock : Prop := DecodeCase [0] [] 0

/-- R2 boundary case: the empty block [0] with positive destination capacity. -/
def emptyBlockPositive : Prop := DecodeCase [0] [] 1

/-- R2 literal-only block: five bytes, exact destination capacity. -/
def literalBlock : Prop := DecodeCase [80, 65, 66, 67, 68, 69] [65, 66, 67, 68, 69] 5

/-- R2 overlapping match: one A, seven copies at offset 1, then BCDEF.
The last match starts exactly 12 bytes before the decoded end. -/
def overlappingMatch : Prop :=
  DecodeCase [19, 65, 1, 0, 80, 66, 67, 68, 69, 70]
    [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70] 13

/-- R2 literal-length extension: the mandatory extension byte 0 after a high nibble 15. -/
def extendedLiterals : Prop :=
  DecodeCase [240, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
    [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79] 15

/-- R2 match-length extension: one A, nineteen copies at offset 1, then BCDEF. -/
def extendedMatch : Prop :=
  DecodeCase [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70]
    (List.replicate 20 65 ++ [66, 67, 68, 69, 70]) 25

/-- R3 offset-zero exception: seven zero match bytes followed by ABCDE,
even though the destination initially holds 0xA5. This is an accepted invalid-format block. -/
def zeroOffset : Prop :=
  DecodeCase [3, 0, 0, 80, 65, 66, 67, 68, 69]
    [0, 0, 0, 0, 0, 0, 0, 65, 66, 67, 68, 69] 12

/-- R3 boundary: an empty compressed buffer is rejected with -1. -/
def emptySource : Prop :=
  Returns Lifted.module "LZ4_decompress_safe" [.i32 131072, .i32 196608, .i32 0, .i32 1]
    [.i32 4294967295]

/-- R2/R3 boundary: at zero capacity, each possible one-byte input is accepted exactly
when it is byte 0. This quantifies over all 256 byte values. -/
def zeroCapacityByte : Prop := ∀ b : UInt8,
  ReturnsAfterWrite Lifted.module 131072 [b] "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 1, .i32 0]
    [.i32 (if b = 0 then 0 else 4294967295)]

end Proofs
