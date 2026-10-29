import FVA.Spec.CAbi
import Proofs.Lifted

/-! Claims: `Prop`-valued definitions about the artifact, read by a reviewer. Import only
FVA's specs and the lifted artifact here; proofs go to `Proof.lean`. -/

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec

/-- The shipped module has a fresh initialized instance under every host semantics. -/
def initializes : Prop := Instantiable Lifted.module

/-- Partial result for R1: with zero input length, every call returns -1 and preserves
the entire store, for every pointer and capacity after any caller write to any fresh instance. This is a
postcondition; it does not assert the absence of reads, or R1 for nonempty inputs. -/
def empty_input_preserves_store : Prop :=
  Instantiable Lifted.module ∧
  ∀ H s inst, Instance Lifted.module H s inst →
    ∀ src dst cap : BitVec 32,
      ∀ (p : Nat) (bytes : List UInt8),
      CallReturns H (s.withBytes p bytes) inst "lz4_decompress"
        [.i32 src, .i32 dst, .i32 0, .i32 cap]
        (fun s' vs => s' = s.withBytes p bytes ∧ vs = [.i32 4294967295])

/-- A concrete execution obligation; a negative result asserts no destination content. -/
def Example : Type := List UInt8 × Nat × BitVec 32 × List UInt8

def Example.input (e : Example) : List UInt8 := e.1
def Example.cap (e : Example) : Nat := e.2.1
def Example.result (e : Example) : BitVec 32 := e.2.2.1
def Example.output (e : Example) : List UInt8 := e.2.2.2

/-- Concrete cases covering literals, length extensions, matches, the fast path, and errors.
These are finite examples, not a definition of the LZ4 language. -/
def examples : List Example :=
  [⟨[], 0, 4294967295, []⟩,
   ⟨[0], 0, 0, []⟩,
   ⟨[80, 97, 98, 99, 100, 101], 5, 5, [97, 98, 99, 100, 101]⟩,
   ⟨[240, 0] ++ List.replicate 15 97, 15, 15, List.replicate 15 97⟩,
   ⟨[19, 97, 1, 0, 80, 98, 99, 100, 101, 102], 13, 13,
     List.replicate 8 97 ++ [98, 99, 100, 101, 102]⟩,
   ⟨[16, 97, 1, 0, 224] ++ List.replicate 14 98, 64, 19,
     List.replicate 5 97 ++ List.replicate 14 98⟩,
   ⟨[64, 97, 98, 99, 100, 4, 0, 128] ++ List.replicate 8 101, 64, 16,
     [97, 98, 99, 100, 97, 98, 99, 100] ++ List.replicate 8 101⟩,
   ⟨[240], 64, 4294967295, []⟩,
   ⟨[240, 255], 64, 4294967295, []⟩,
   ⟨[32, 97], 64, 4294967295, []⟩,
   ⟨[16, 97, 1], 64, 4294967295, []⟩,
   ⟨[16, 97, 0, 0, 0], 64, 4294967295, []⟩,
   ⟨[16, 97, 2, 0, 0], 64, 4294967295, []⟩,
   ⟨[31, 97, 1, 0], 64, 4294967295, []⟩,
   ⟨[80, 97, 98, 99, 100, 101], 4, 4294967295, []⟩,
   ⟨[19, 97, 1, 0, 80, 98, 99, 100, 101, 102], 7, 4294967295, []⟩]

/-- All fresh instances return the specified result after writing the concrete input at
131072, with destination 262144. On success, every returned output byte is checked.
The buffers satisfy the README's domain. This is only a finite subset of R2/R3. -/
def ExampleCorrect (e : Example) : Prop :=
  131072 + e.input.length ≤ 262144 ∧ 262144 + e.cap ≤ 2097152 ∧
  (e.result.toNat < 2147483648 → e.result.toNat = e.output.length ∧ e.output.length ≤ e.cap) ∧
  (∀ H, ∃ s inst, Instance Lifted.module H s inst ∧
    Fits s 131072 e.input.length ∧ Fits s 262144 e.cap) ∧
  ∀ H s inst, Instance Lifted.module H s inst →
    CallReturns H (s.withBytes 131072 e.input) inst "lz4_decompress"
      [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 e.input.length),
        .i32 (BitVec.ofNat 32 e.cap)]
      (fun s' vs => vs = [.i32 e.result] ∧ ∃ mem, s'.mems[0]? = some mem ∧
        (List.range e.output.length).map (fun i => mem.byte (262144 + i)) = e.output)

/-- Partial results for R2/R3: every case in `examples` satisfies `ExampleCorrect`.
No universal claim about arbitrary compressed blocks is made. -/
def concrete_examples : Prop := ∀ e ∈ examples, ExampleCorrect e

end Proofs
