import Proofs.Lifted
import FVA.Spec.CAbi
import FVA.Spec.Valid.Module

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- The allocation's module instance, including the artifact's exported function addresses. -/
noncomputable def initialInst : ModuleInst :=
  (allocModule {} Lifted.module [] [.i32 65536] []).2

/-- The initialized store: the artifact's active data segment is copied to 65536 and dropped. -/
noncomputable def initialStore : Store :=
  let a := (allocModule {} Lifted.module [] [.i32 65536] []).1
  let data := ((Lifted.module.datas[0]?).getD (⟨[], .passive⟩ : Data)).init
  let emptyMem : MemInst := { pages := 0, max := none, byte := fun _ => 0 }
  let mem := data.zipIdx.foldl (fun (m : MemInst) (b, i) =>
    m.write (65536 + i) 1 b.toNat) ((a.mems[0]?).getD emptyMem)
  { a with mems := [mem], datas := [{ data := [] }] }

/-- The specified initialized state is a successful fresh instance of the exact artifact,
under every host behavior. This is infrastructure, not a proof of R1, R2, or R3. -/
def initialization : Prop :=
  ∀ H, Instance Lifted.module H initialStore initialInst

/-- R2 special case: the empty block 00 with zero destination capacity, at fixed disjoint
caller addresses, always returns zero and changes no store state during the call. -/
def emptyBlock : Prop :=
  ∀ H, CallReturns H (initialStore.withBytes 131072 [0]) initialInst
    "LZ4_decompress_safe" [.i32 131072, .i32 196608, .i32 1, .i32 0]
    (fun s vs => vs = [.i32 0] ∧ s = initialStore.withBytes 131072 [0])

/-- A caller-supplied memory, with the artifact's functions and initialized non-memory state. -/
noncomputable def callerStore (mem : MemInst) : Store :=
  { initialStore with mems := [mem] }

/-- Complete behavior of the zero-capacity branch for arbitrary memory and pointers.
The source pointer is nonzero and its first byte is in memory. The source size may be any i32.
A successful return occurs exactly when the size is one and that byte is zero; the final store
equals the initial store. This is a restricted R2/R3 result, not full R1/R2/R3. -/
def zeroCapacity : Prop :=
  ∀ H (mem : MemInst) (src dst n : BitVec 32),
    src ≠ 0 → src.toNat < mem.size →
    CallReturns H (callerStore mem) initialInst "LZ4_decompress_safe"
      [.i32 src, .i32 dst, .i32 n, .i32 0]
      (fun s vs => s = callerStore mem ∧
        vs = [.i32 (if n = BitVec.ofNat 32 1 ∧ mem.byte src.toNat = 0 then 0 else -1)])


/-- Source and destination setup for the concrete cases. The destination starts filled with A5. -/
noncomputable def caseStore (input : List UInt8) (capacity : Nat) : Store :=
  (initialStore.withBytes 196608 (List.replicate capacity 165)).withBytes 131072 input

/-- Concrete literal case: input 1041, capacity 1, return 1,
output 41. This is an example, not a universal format-correctness claim. -/
def literalCase : Prop :=
  ∀ H, CallReturns H (caseStore [16, 65] 1) initialInst "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 2, .i32 1]
    (fun s vs => vs = [.i32 1] ∧ ∃ mem, s.mems[0]? = some mem ∧
      (List.range 1).map (fun i => mem.byte (196608 + i)) = [65])

/-- Concrete overlap case: input 13410100504243444546, capacity 13, return 13,
output 41414141414141414243444546. This is an example, not a universal format-correctness claim. -/
def overlapCase : Prop :=
  ∀ H, CallReturns H (caseStore [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13) initialInst "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 10, .i32 13]
    (fun s vs => vs = [.i32 13] ∧ ∃ mem, s.mems[0]? = some mem ∧
      (List.range 13).map (fun i => mem.byte (196608 + i)) = [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70])

/-- Concrete longMatch case: input 1f41010001504243444546, capacity 26, return 26,
output 4141414141414141414141414141414141414141414243444546. This is an example, not a universal format-correctness claim. -/
def longMatchCase : Prop :=
  ∀ H, CallReturns H (caseStore [31, 65, 1, 0, 1, 80, 66, 67, 68, 69, 70] 26) initialInst "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 11, .i32 26]
    (fun s vs => vs = [.i32 26] ∧ ∃ mem, s.mems[0]? = some mem ∧
      (List.range 26).map (fun i => mem.byte (196608 + i)) = [65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70])

/-- Concrete zeroOffset case: input 030000504243444546, capacity 12, return 12,
output 000000000000004243444546. This is an example, not a universal format-correctness claim. -/
def zeroOffsetCase : Prop :=
  ∀ H, CallReturns H (caseStore [3, 0, 0, 80, 66, 67, 68, 69, 70] 12) initialInst "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 9, .i32 12]
    (fun s vs => vs = [.i32 12] ∧ ∃ mem, s.mems[0]? = some mem ∧
      (List.range 12).map (fun i => mem.byte (196608 + i)) = [0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70])

/-- Concrete shortcut case: input 8341424344454647480800f0006162636465666768696a6b6c6d6e6f, capacity 64, return 30,
output 4142434445464748414243444546476162636465666768696a6b6c6d6e6f. This is an example, not a universal format-correctness claim. -/
def shortcutCase : Prop :=
  ∀ H, CallReturns H (caseStore [131, 65, 66, 67, 68, 69, 70, 71, 72, 8, 0, 240, 0, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111] 64) initialInst "LZ4_decompress_safe"
    [.i32 131072, .i32 196608, .i32 28, .i32 64]
    (fun s vs => vs = [.i32 30] ∧ ∃ mem, s.mems[0]? = some mem ∧
      (List.range 30).map (fun i => mem.byte (196608 + i)) = [65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 69, 70, 71, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111])

/-- The exact artifact satisfies FVA's WebAssembly module-validity judgment.
This checks Wasm typing, not the LZ4 format or the caller's buffer boundaries. -/
def validModule : Prop := FVA.Wasm.Valid.ModuleValid Lifted.module

end Proofs
