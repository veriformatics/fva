import Proofs.Lifted
import FVA.Spec.CAbi

/-! Partial verification only: these claims do not assert all of README R1, R2 or R3. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- Observe exactly `n` bytes of memory 0, or `none` if memory 0 does not exist. -/
def bytesAt (s : Store) (p n : Nat) : Option (List UInt8) :=
  s.mems[0]?.map fun mem => (List.range n).map fun i => mem.byte (p + i)

/-- A concrete execution case. Negative results use their signed i32 representation. -/
abbrev Case := List UInt8 × Nat × Int × List UInt8

def Case.input (c : Case) : List UInt8 := c.1
def Case.capacity (c : Case) : Nat := c.2.1
def Case.result (c : Case) : Int := c.2.2.1
def Case.output (c : Case) : List UInt8 := c.2.2.2

/-- Input at 131072, destination at 196608; eight guard bytes on either side of the
capacity, together with the destination, are initialized to 165 before the call. -/
def prepared (s : Store) (c : Case) : Store :=
  (s.withBytes 131072 c.input).withBytes 196600 (List.replicate (c.capacity + 16) 165)

/-- Every execution returns the expected signed i32, produces the specified output,
preserves the input, and preserves the two eight-byte guards. This observes guards,
not all out-of-bounds accesses. Quantifies over every fresh instance and host semantics. -/
def caseCorrect (c : Case) : Prop :=
  ∀ H s inst, Instance Lifted.module H s inst →
    CallReturns H (prepared s c) inst "LZ4_decompress_safe"
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 c.input.length),
       .i32 (BitVec.ofNat 32 c.capacity)] fun s' vs =>
      vs = [.i32 (BitVec.ofInt 32 c.result)] ∧
      bytesAt s' 196608 c.output.length = some c.output ∧
      bytesAt s' 131072 c.input.length = some c.input ∧
      bytesAt s' 196600 8 = some (List.replicate 8 165) ∧
      bytesAt s' (196608 + c.capacity) 8 = some (List.replicate 8 165)

/-- Empty input, empty output, literals, extended literal lengths, overlapping and
nonoverlapping matches, offset zero, truncated blocks, and an invalid backwards offset.
Their format interpretations are spelled out in VERIFICATION.md. -/
def cases : List Case := [
  ⟨[0], 0, 0, []⟩,
  ⟨[0], 1, 0, []⟩,
  ⟨[16, 65], 1, 1, [65]⟩,
  ⟨[240, 0] ++ (List.range 15).map UInt8.ofNat, 15, 15,
    (List.range 15).map UInt8.ofNat⟩,
  ⟨[240, 255, 0] ++ List.replicate 270 65, 270, 270, List.replicate 270 65⟩,
  ⟨[24, 65, 1, 0, 80, 66, 67, 68, 69, 70], 18, 18,
    List.replicate 13 65 ++ [66, 67, 68, 69, 70]⟩,
  ⟨[131, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 80, 20, 21, 22, 23, 24], 20, 20,
    [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 20, 21, 22, 23, 24]⟩,
  ⟨[8, 0, 0, 80, 66, 67, 68, 69, 70], 17, 17,
    List.replicate 12 0 ++ [66, 67, 68, 69, 70]⟩,
  ⟨[8, 1, 0, 80, 66, 67, 68, 69, 70], 17, -4, []⟩,
  ⟨[240], 32, -2, []⟩,
  ⟨[16], 1, -2, []⟩,
  ⟨[], 1, -1, []⟩,
  ⟨[0, 0, 0, 80, 66, 67, 68, 69, 70], 12, 9,
    [0, 0, 0, 0, 66, 67, 68, 69, 70]⟩]

/-- An empty compressed input always returns -1, with the whole store unchanged.
Allows arbitrary arguments and arbitrary caller bytes written at address zero. This
proves an early-return family, not general decoding correctness or read safety. -/
def zeroInputRejected : Prop :=
  Instantiable Lifted.module ∧
    ∀ H s inst, Instance Lifted.module H s inst →
      ∀ (src dst capacity : BitVec 32) (memory : List UInt8),
        CallReturns H (s.withBytes 0 memory) inst "LZ4_decompress_safe"
          [.i32 src, .i32 dst, .i32 0, .i32 capacity] fun s' vs =>
          s' = s.withBytes 0 memory ∧ vs = [.i32 4294967295]

/-- Partial R2/R3 evidence and finite guard observations relevant to R1: all listed
cases execute correctly. Includes instantiability to exclude vacuity. This is not a
universal LZ4 correctness or memory-access-safety claim. -/
def regressionCases : Prop :=
  Instantiable Lifted.module ∧ ∀ c ∈ cases, caseCorrect c

end Proofs
