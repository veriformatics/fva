import Proofs.Lifted
import FVA.Spec.CAbi

/-! Partial verification only: the claims below cover the listed calls, not all of R1–R3. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

/-- Allocate the artifact's code and its actual initial global. -/
noncomputable def allocation : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []

/-- The artifact's runtime, with arbitrary memory bytes and its data segment dropped.
The existence claim below establishes that a genuine fresh instance has this form. -/
noncomputable def runtime (bytes : Nat → UInt8) : Store :=
  { allocation.1 with
    mems := [{ pages := 32, max := some 32, byte := bytes }]
    datas := [{ data := [] }] }

/-- Read/write traffic of the next memory instruction. -/
abbrev Access := Bool × Nat × Nat
def Access.write (a : Access) : Bool := a.1
def Access.addr (a : Access) : Nat := a.2.1
def Access.count (a : Access) : Nat := a.2.2

/-- Operand stacks are top first. Bulk operations include every byte of their ranges. -/
def instructionAccess (i : Instr) (vs : List Val) : List Access :=
  match i, vs with
  | .load t m, .i32 a :: _ => [⟨false, a.toNat + m.offset, t.bytes⟩]
  | .loadPacked _ p _ m, .i32 a :: _ => [⟨false, a.toNat + m.offset, p.bits / 8⟩]
  | .store t m, _ :: .i32 a :: _ => [⟨true, a.toNat + m.offset, t.bytes⟩]
  | .storePacked _ p m, _ :: .i32 a :: _ => [⟨true, a.toNat + m.offset, p.bits / 8⟩]
  | .memoryCopy, .i32 n :: .i32 s :: .i32 d :: _ =>
      [⟨false, s.toNat, n.toNat⟩, ⟨true, d.toNat, n.toNat⟩]
  | .memoryFill, .i32 n :: _ :: .i32 d :: _
  | .memoryInit _, .i32 n :: _ :: .i32 d :: _ => [⟨true, d.toNat, n.toNat⟩]
  | _, _ => []

/-- Canonical operand constants, as in the Wasm value grammar. -/
def constantVal : AInstr → Option Val
  | .plain (.iconst .w32 n) => if n < 2^32 then some (.i32 (BitVec.ofNat 32 n)) else none
  | .plain (.iconst .w64 n) => if n < 2^64 then some (.i64 (BitVec.ofNat 64 n)) else none
  | .plain (.fconst .w32 n) => if n < 2^32 then some (.f32 (BitVec.ofNat 32 n)) else none
  | .plain (.fconst .w64 n) => if n < 2^64 then some (.f64 (BitVec.ofNat 64 n)) else none
  | .plain (.refNull t) => some (.ref (.null t))
  | .refFuncAddr a => some (.ref (.func a))
  | .refExternAddr a => some (.ref (.extern a))
  | _ => none

mutual
/-- Find the next instruction, descending through administrative frames and labels. -/
def nextAccess (vs : List Val) : List AInstr → List Access
  | [] => []
  | e :: es => match constantVal e with
    | some v => nextAccess (v :: vs) es
    | none => atAccess vs e
/-- Traffic of the next non-value redex. -/
def atAccess (vs : List Val) : AInstr → List Access
  | .label _ _ body | .frame _ _ body => nextAccess [] body
  | .plain i => instructionAccess i vs
  | _ => []
end

/-- R1's address restriction, checked byte by byte. Addresses outside the README's
caller region are unrestricted by R1. Input and output addresses here are fixed. -/
def accessSafe (n cap : Nat) (a : Access) : Bool :=
  (List.range a.count).all fun k =>
    let p := a.addr + k
    decide ((131072 ≤ p ∧ p < 2097152) →
      (262144 ≤ p ∧ p < 262144 + cap) ∨
      (a.write = false ∧ 131072 ≤ p ∧ p < 131072 + n))

/-- Safety of all memory traffic at the next redex, including bulk operations. -/
def configSafe (n cap : Nat) (c : Config) : Bool :=
  (nextAccess [] c.instrs).all (accessSafe n cap)

/-- Read consecutive bytes of memory 0. -/
def outputBytes (s : Store) (n : Nat) : Option (List UInt8) :=
  s.mems[0]?.map fun m => (List.range n).map fun k => m.byte (262144 + k)

/-- Exact ABI arguments for a sample at src=131072 and dst=262144. -/
def arguments (input : List UInt8) (cap : Nat) : List Val :=
  [.i32 131072, .i32 262144, .i32 (BitVec.ofNat 32 input.length), .i32 (BitVec.ofNat 32 cap)]

/-- Total return and exact output for this input/capacity, after zeroing the output
buffer, for every surrounding memory byte function and every host semantics; and R1's access restriction at every state
reachable under the Wasm semantics. Failure samples specify an empty output observation,
so they assert the error return and traffic safety, not absence of partial writes. -/
def Sample (input : List UInt8) (cap : Nat) (result : BitVec 32) (output : List UInt8) : Prop :=
  ∀ (bytes : Nat → UInt8) (H : HostSem),
    let s := ((runtime bytes).withBytes 262144 (List.replicate cap 0)).withBytes 131072 input
    CallReturns H s allocation.2 "lz4_decompress" (arguments input cap)
      (fun s' vs => vs = [.i32 result] ∧ outputBytes s' output.length = some output) ∧
    ∀ c, Steps H (invokeConfig s 7 (arguments input cap)) c → configSafe input.length cap c = true

/-- Nonvacuity: under every host behavior a genuine initialized fresh instance has
exactly the runtime code, globals, memory size, and dropped segment used in Sample. -/
def fresh_runtime : Prop :=
  ∀ H, ∃ bytes, Instance Lifted.module H (runtime bytes) allocation.2

/-- Zero compressed bytes return -1 without changing any state, for arbitrary pointers,
capacity, store and host, provided function 7 contains the artifact's decoder code. -/
def zero_input : Prop :=
  ∀ (s : Store) (inst : ModuleInst) (src dst cap : BitVec 32) (H : HostSem),
    s.funcs[7]? = some (.wasm (Lifted.module.types[4]?.getD ⟨[], []⟩) inst Lifted.func7) →
    Must H (fun | .returned s' vs => s' = s ∧ vs = [.i32 4294967295]
                | .trapped _ => False)
      (invokeConfig s 7 [.i32 src, .i32 dst, .i32 0, .i32 cap])

/-- Valid encoding of the empty content. -/
def empty_block : Prop := Sample [0] 0 0 []
/-- A valid literal-only block. -/
def hello_block : Prop := Sample [80, 104, 101, 108, 108, 111] 5 5 [104, 101, 108, 108, 111]
/-- Literal length 15 requires an explicit zero extension byte. -/
def extended_literals : Prop :=
  Sample ([240, 0] ++ List.range 15 |>.map UInt8.ofNat) 15 15 ((List.range 15).map UInt8.ofNat)
/-- A valid independent block with an overlapping offset-1 match (1+7+5 bytes). -/
def overlap_one : Prop :=
  Sample [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] 13 13
    [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70]
/-- A valid independent block with an overlapping offset-2 match (2+7+5 bytes). -/
def overlap_two : Prop :=
  Sample [35, 65, 66, 2, 0, 80, 67, 68, 69, 70, 71] 14 14
    [65, 66, 65, 66, 65, 66, 65, 66, 65, 67, 68, 69, 70, 71]
/-- Match length 19 uses an explicit zero extension byte. -/
def extended_match : Prop :=
  Sample [31, 65, 1, 0, 0, 80, 66, 67, 68, 69, 70] 25 25
    (List.replicate 20 65 ++ [66, 67, 68, 69, 70])
/-- The fast path: 16-byte literal copy followed by an overlapping match. -/
def fast_overlap : Prop :=
  Sample ([16, 65, 1, 0, 240, 20] ++ List.replicate 35 66) 40 40
    (List.replicate 5 65 ++ List.replicate 35 66)
/-- The fast path: 16-byte literal copy followed by an 18-byte match copy. -/
def fast_wild_copy : Prop :=
  Sample ([64, 65, 66, 67, 68, 4, 0, 240, 20] ++ List.replicate 35 69) 64 43
    ([65, 66, 67, 68, 65, 66, 67, 68] ++ List.replicate 35 69)
/-- Missing literal-length extension is rejected. -/
def truncated_length : Prop := Sample [240] 32 4294967295 []
/-- Offset zero is invalid and is rejected. -/
def zero_offset : Prop := Sample [16, 65, 0, 0] 32 4294967295 []
/-- A match cannot refer before this independent block. -/
def external_offset : Prop := Sample [0, 1, 0] 32 4294967295 []
/-- Truncated literals are rejected. -/
def truncated_literals : Prop := Sample [32, 65] 32 4294967295 []
/-- A one-byte offset field is rejected. -/
def truncated_offset : Prop := Sample [0, 1] 32 4294967295 []
/-- Insufficient literal output capacity is rejected. -/
def small_capacity : Prop := Sample [80, 104, 101, 108, 108, 111] 4 4294967295 []

/-- End-condition relaxation permitted by R3: the final literal sequence is empty. -/
def relaxed_end : Prop := Sample [16, 65, 1, 0, 0] 5 5 (List.replicate 5 65)
/-- The slow path's 32-byte match copy, with only four bytes logically appended. -/
def wide32 : Prop :=
  Sample ([240, 17] ++ (List.range 32).map UInt8.ofNat ++ [32, 0, 240, 20] ++
    List.replicate 35 69) 71 71
    ((List.range 32).map UInt8.ofNat ++ [0, 1, 2, 3] ++ List.replicate 35 69)
/-- The slow path's 64-byte match copy, with 33 bytes logically appended. -/
def wide64 : Prop :=
  Sample ([255, 49] ++ (List.range 64).map UInt8.ofNat ++ [64, 0, 14, 240, 20] ++
    List.replicate 35 69) 132 132
    ((List.range 64).map UInt8.ofNat ++ (List.range 33).map UInt8.ofNat ++ List.replicate 35 69)

end Proofs
