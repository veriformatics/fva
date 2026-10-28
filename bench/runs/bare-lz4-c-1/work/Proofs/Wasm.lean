import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.RCases

/- Executable semantics for the integer-only, single-memory fragment used by
   functions 2, 3 and 4. Control labels are resolved by extract.py. -/
namespace Wasm

def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def bool (p : Prop) [Decidable p] : Nat := if p then 1 else 0

inductive Bin where
  | add | sub | and | xor | shl | shr | eq | ne | ltu | leu | gtu | geu | lts
  deriving DecidableEq, Repr

def binary : Bin → Nat → Nat → Nat
  | .add, a, b => word (a + b)
  | .sub, a, b => word (a + modulus - b)
  | .and, a, b => Nat.land a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => word (a * 2 ^ (b % 32))
  | .shr, a, b => a / 2 ^ (b % 32)
  | .eq, a, b => bool (a = b)
  | .ne, a, b => bool (a ≠ b)
  | .ltu, a, b => bool (a < b)
  | .leu, a, b => bool (a ≤ b)
  | .gtu, a, b => bool (a > b)
  | .geu, a, b => bool (a ≥ b)
  | .lts, a, b => bool ((a + 2147483648) % modulus < (b + 2147483648) % modulus)

inductive Instr where
  | const (v : Nat) | get (i : Nat) | set (i : Nat) | tee (i : Nat)
  | eqz | bin (op : Bin) | drop | select
  | load (width offset : Nat) | store (width offset : Nat)
  | jump (pc : Nat) | jumpIf (pc : Nat) | call (id : Nat) | ret
  deriving DecidableEq, Repr

structure Func where
  params : Nat
  locals : Nat
  code : Nat → Option Instr

structure Access where
  write : Bool
  addr : Nat
  width : Nat
  deriving DecidableEq, Repr

abbrev Memory := Nat → Nat
structure Frame where
  id : Nat
  pc : Nat := 0
  locals : List Nat
  stack : List Nat := []

inductive Status where
  | active | halted (value : Nat) | trap
  deriving DecidableEq, Repr

structure State where
  frame : Frame
  callers : List Frame := []
  mem : Memory
  trace : List Access := [] -- newest access first
  status : Status := .active

def readLE (mem : Memory) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mem addr % 256 + 256 * readLE mem (addr + 1) n

def writeLE (mem : Memory) (addr value : Nat) : Nat → Memory
  | 0 => mem
  | n + 1 => writeLE (fun a => if a = addr then value % 256 else mem a)
      (addr + 1) (value / 256) n

def initial (mem : Memory) (src dst size cap : Nat) : State :=
  { frame := { id := 2, locals := [src, dst, size, cap] ++ List.replicate 15 0 }, mem }

def step (program : Nat → Func) (s : State) : State := Id.run do
  if s.status != .active then return s
  let f := s.frame
  let next := { f with pc := f.pc + 1 }
  let fail := { s with status := .trap }
  let some ins := (program f.id).code f.pc | return fail
  match ins with
  | .const v => return { s with frame := { next with stack := v :: f.stack } }
  | .get i =>
    let some v := f.locals[i]? | return fail
    return { s with frame := { next with stack := v :: f.stack } }
  | .set i | .tee i =>
    let v :: rest := f.stack | return fail
    if i ≥ f.locals.length then return fail
    let st := if ins == .tee i then f.stack else rest
    return { s with frame := { next with locals := f.locals.set i v, stack := st } }
  | .eqz =>
    let v :: rest := f.stack | return fail
    return { s with frame := { next with stack := bool (v = 0) :: rest } }
  | .bin op =>
    let b :: a :: rest := f.stack | return fail
    return { s with frame := { next with stack := binary op a b :: rest } }
  | .drop =>
    let _ :: rest := f.stack | return fail
    return { s with frame := { next with stack := rest } }
  | .select =>
    let c :: b :: a :: rest := f.stack | return fail
    return { s with frame := { next with stack := (if c = 0 then b else a) :: rest } }
  | .load width offset =>
    let a :: rest := f.stack | return fail
    let addr := a + offset
    if addr + width > 2097152 then return fail
    return { s with
      frame := { next with stack := readLE s.mem addr width :: rest }
      trace := ⟨false, addr, width⟩ :: s.trace }
  | .store width offset =>
    let v :: a :: rest := f.stack | return fail
    let addr := a + offset
    if addr + width > 2097152 then return fail
    return { s with
      frame := { next with stack := rest }
      mem := writeLE s.mem addr v width
      trace := ⟨true, addr, width⟩ :: s.trace }
  | .jump pc => return { s with frame := { f with pc } }
  | .jumpIf pc =>
    let v :: rest := f.stack | return fail
    return { s with frame := { f with pc := if v = 0 then next.pc else pc, stack := rest } }
  | .call id =>
    let callee := program id
    if f.stack.length < callee.params then return fail
    let locals := (f.stack.take callee.params).reverse ++ List.replicate callee.locals 0
    return { s with
      frame := { id, locals }
      callers := { next with stack := f.stack.drop callee.params } :: s.callers }
  | .ret =>
    let [v] := f.stack | return fail
    match s.callers with
    | [] => return { s with status := .halted v }
    | caller :: rest => return { s with
        frame := { caller with stack := v :: caller.stack }, callers := rest }

def run (program : Nat → Func) : Nat → State → State :=
  Nat.rec (fun s => s) (fun _ previous s =>
    if s.status == .active then previous (step program s) else s)

def inRange (a width base size : Nat) : Prop := base ≤ a ∧ a + width ≤ base + size
def accessOK (src dst size cap : Nat) (a : Access) : Prop :=
  a.addr + a.width ≤ 131072 ∨
  (if a.write then inRange a.addr a.width dst cap
   else inRange a.addr a.width src size ∨ inRange a.addr a.width dst cap)

instance (src dst size cap : Nat) (a : Access) : Decidable (accessOK src dst size cap a) := by
  unfold accessOK inRange
  infer_instance

end Wasm
