import FVA.Spec.CAbi

/-! Reviewed access specification. The stack is top first. A memory operation's
entire byte range is checked, including bytes copied speculatively. -/
namespace Proofs
open FVA.Wasm FVA.Wasm.Exec

def literalValue : AInstr → Option Val
  | .plain (.iconst .w32 n) => bif Nat.blt n (2 ^ 32) then some (.i32 (BitVec.ofNat 32 n)) else none
  | .plain (.iconst .w64 n) => bif Nat.blt n (2 ^ 64) then some (.i64 (BitVec.ofNat 64 n)) else none
  | .plain (.fconst .w32 n) => bif Nat.blt n (2 ^ 32) then some (.f32 (BitVec.ofNat 32 n)) else none
  | .plain (.fconst .w64 n) => bif Nat.blt n (2 ^ 64) then some (.f64 (BitVec.ofNat 64 n)) else none
  | .plain (.refNull t) => some (.ref (.null t))
  | .refFuncAddr a => some (.ref (.func a))
  | .refExternAddr a => some (.ref (.extern a))
  | _ => none

structure Access where
  write : Bool
  address : Nat
  width : Nat

def instructionAccesses (i : Instr) (stack : List Val) : List Access :=
  match i, stack with
  | .load t m, .i32 a :: _ => [⟨false, a.toNat + m.offset, t.bytes⟩]
  | .loadPacked _ p _ m, .i32 a :: _ => [⟨false, a.toNat + m.offset, p.bits / 8⟩]
  | .store t m, _ :: .i32 a :: _ => [⟨true, a.toNat + m.offset, t.bytes⟩]
  | .storePacked _ p m, _ :: .i32 a :: _ => [⟨true, a.toNat + m.offset, p.bits / 8⟩]
  | .memoryFill, .i32 n :: _ :: .i32 d :: _ => [⟨true, d.toNat, n.toNat⟩]
  | .memoryCopy, .i32 n :: .i32 s :: .i32 d :: _ =>
      [⟨false, s.toNat, n.toNat⟩, ⟨true, d.toNat, n.toNat⟩]
  | .memoryInit _, .i32 n :: _ :: .i32 d :: _ => [⟨true, d.toNat, n.toNat⟩]
  | _, _ => []

mutual
  def pendingAccesses (stack : List Val) : List AInstr → List Access
    | [] => []
    | e :: rest => match literalValue e with
      | some v => pendingAccesses (v :: stack) rest
      | none => activeAccesses stack e
  def activeAccesses (stack : List Val) : AInstr → List Access
    | .plain i => instructionAccesses i stack
    | .label _ _ body | .frame _ _ body => pendingAccesses [] body
    | _ => []
end

/-- Addresses below the caller area are unrestricted by R1. Above it, every read
must lie in one of the two buffers; every write must lie in the destination. -/
def accessAllowed (src dst srcSize capacity : Nat) (a : Access) : Bool :=
  (List.range a.width).all fun j =>
    let p := a.address + j
    p < 131072 || (dst ≤ p && p < dst + capacity) ||
      (!a.write && src ≤ p && p < src + srcSize)

def accessesAllowed (src dst srcSize capacity : Nat) (c : Config) : Bool :=
  (pendingAccesses [] c.instrs).all (accessAllowed src dst srcSize capacity)

/-- A property holds at every reachable configuration, including intermediate
states inside memcpy and memmove. -/
def Throughout (H : HostSem) (I : Config → Prop) (c : Config) : Prop :=
  ∀ c', Steps H c c' → I c'
end Proofs
