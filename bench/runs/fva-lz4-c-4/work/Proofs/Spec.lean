import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- A concrete run from a fresh instance, for every host semantics. The caller fills the
destination and its two guard bytes with 165, then writes the compressed input at 131072.
The call must terminate without trapping, return `ret`, produce `output`, preserve both
guards, and preserve the compressed input. This is an existential fresh-instance claim;
it is NOT any of the universal requirements R1--R3. -/
def Example (input : List UInt8) (capacity : Nat) (ret : BitVec 32)
    (output : List UInt8) : Prop :=
  ∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
    Fits s 131072 input.length ∧ Fits s 262143 (capacity + 2) ∧
    CallReturns H ((s.withBytes 262143 (List.replicate (capacity + 2) 165)).withBytes
      131072 input) inst "LZ4_decompress_safe"
      [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 input.length),
        .i32 (BitVec.ofNat 32 capacity)]
      (fun s' vs => vs = [.i32 ret] ∧ ∃ mem, s'.mems[0]? = some mem ∧
        (List.range output.length).map (fun k => mem.byte (262144 + k)) = output ∧
        mem.byte 262143 = 165 ∧ mem.byte (262144 + capacity) = 165 ∧
        (List.range input.length).map (fun k => mem.byte (131072 + k)) = input)

/-- R2/R3 boundary example: the one-byte empty block succeeds with zero capacity. -/
def empty_zero : Prop := Example [0] 0 0 []

/-- R2/R3 example: the empty block succeeds with capacity one. -/
def empty_positive : Prop :=
  Example [0] 1 0 []

/-- Malformed-input example: no compressed bytes returns negative one. -/
def no_input : Prop :=
  Example [] 1 (-1) []

/-- R2/R3 example: a single literal A decodes exactly. -/
def literal : Prop :=
  Example [16, 65] 1 1 [65]

/-- R2/R3 example: offset one generates an overlapping twelve-byte match. -/
def overlap : Prop :=
  Example [24, 65, 1, 0, 80, 66, 67, 68, 69, 70] 18 18 [65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]

/-- R2/R3 example: a zero extension byte encodes fifteen literals. -/
def literal_extension : Prop :=
  Example [240, 0, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79] 15 15 [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]

/-- R2/R3 example: a zero extension byte encodes a nineteen-byte match. -/
def match_extension : Prop :=
  Example [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70] 25 25 [65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]

/-- R3 permitted departure: offset zero generates twelve zero bytes. -/
def zero_offset : Prop :=
  Example [8, 0, 0, 80, 66, 67, 68, 69, 70] 17 17 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70]

/-- Malformed-input example: offset one before any output returns negative four. -/
def bad_offset : Prop :=
  Example [8, 1, 0, 80, 66, 67, 68, 69, 70] 17 (-4) []

/-- Malformed-input example: a missing literal returns negative two. -/
def truncated : Prop :=
  Example [16] 1 (-2) []

/-- Capacity example: two literals with capacity one returns negative two. -/
def too_small : Prop :=
  Example [32, 65, 66] 1 (-2) []

/-- R2/R3 example exercising the sixteen-byte literal and eighteen-byte match shortcuts. -/
def shortcut : Prop :=
  Example [128, 65, 66, 67, 68, 69, 70, 71, 72, 8, 0, 192, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108] 32 24 [65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]

end Proofs
