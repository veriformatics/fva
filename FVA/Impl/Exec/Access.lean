import FVA.Impl.Exec.Ref

/-!
# The memory access of the next step

`access c` = the in-bounds load or store the reference stepper's next step performs, found by
the stepper's own traversal (values onto the stack, into labels and frames, the first non-value);
`FVA.Proof.Exec.Access` proves it equal to the spec's `Reads`/`Writes` (`reads_iff`,
`writes_iff`), so a proof checks a step's footprint by evaluation.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- One memory access: a write or a read of `len` bytes from `start` in the memory at store
address `mem`. -/
structure Access where
  /-- A store (`true`) or a load (`false`). -/
  write : Bool
  /-- The memory's store address. -/
  mem : Nat
  /-- The first byte. -/
  start : Nat
  /-- The byte count. -/
  len : Nat

/-- The access of the in-bounds `n`-byte read (`write = false`) or write at `ea`, if memory 0 of
the frame exists and holds it. -/
def rangeAccess (s : Store) (f : Frame) (write : Bool) (ea n : Nat) : Option Access :=
  match mem0 s f with
  | some (a, mem) => bif Nat.blt mem.size (ea + n) then none else some ⟨write, a, ea, n⟩
  | none => none

/-- The access of instruction `i` with operand stack `vs` (top first). -/
def instrAccess (s : Store) (f : Frame) : Instr → List Val → Option Access
  | .load t m, .i32 i :: _ => rangeAccess s f false (i.toNat + m.offset) t.bytes
  | .loadPacked _ p _ m, .i32 i :: _ => rangeAccess s f false (i.toNat + m.offset) (p.bits / 8)
  | .store t m, v :: .i32 i :: _ => match v.numBits t with
    | some _ => rangeAccess s f true (i.toNat + m.offset) t.bytes
    | none => none
  | .storePacked w p m, v :: .i32 i :: _ => match v.intBits w with
    | some _ => rangeAccess s f true (i.toNat + m.offset) (p.bits / 8)
    | none => none
  | _, _ => none

mutual
/-- The access at the first non-value of `es`; `vs` = the values before it (top first). -/
def seqAccess (s : Store) (f : Frame) (vs : List Val) : List AInstr → Option Access
  | [] => none
  | e :: rest => match toVal e with
    | some v => seqAccess s f (v :: vs) rest
    | none => atAccess s f vs e

/-- The access at the non-value `e`, with values `vs` (top first) before it. -/
def atAccess (s : Store) (f : Frame) (vs : List Val) : AInstr → Option Access
  | .label _ _ body => seqAccess s f [] body
  | .frame _ fi body => seqAccess s fi [] body
  | .plain i => instrAccess s f i vs
  | _ => none
end

/-- The memory access of the next step of `c`, if it has one. -/
def access (c : Config) : Option Access := seqAccess c.store c.frame [] c.instrs

end FVA.Wasm.Exec.Ref
