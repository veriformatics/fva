import Mathlib

/- A small interpreter for the instructions in the decoder. Calls are deliberately
   unsupported: a successful certificate must return without executing one.
   Validated Wasm supplies operand types; words are represented by natural numbers.
   Every load/store (including bulk memory) records its entire accessed range. -/
namespace Wasm

inductive Op where
  | const (n : Nat)
  | get (i : Nat) | set (i : Nat) | tee (i : Nat)
  | add | sub | eq | ne | lt | le | gt | ge | eqz | band | shr | select
  | load (width offset : Nat) | store (width offset : Nat)
  | copy | fill
  | block (endPc : Nat) | loop (endPc : Nat) | end
  | br (depth : Nat) | brIf (depth : Nat)
  | ret | unreachable | unsupported (opcode : Nat)
  deriving Repr, DecidableEq, BEq

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq

structure Label where
  target : Nat
  height : Nat
  isLoop : Bool
  deriving Repr

structure Memory where
  cells : Std.TreeMap Nat Nat := {}

def Memory.read (m : Memory) (a : Nat) : Nat :=
  (m.cells.get? a).getD (if a < 131072 then 0 else 165)

def Memory.write (m : Memory) (a b : Nat) : Memory :=
  ⟨m.cells.insert a (b % 256)⟩

def Memory.writeBytes (m : Memory) (a : Nat) (bytes : List Nat) : Memory :=
  (bytes.foldl (fun (p : Memory × Nat) b => (p.1.write p.2 b, p.2 + 1)) (m, a)).1

def Memory.readBytes (m : Memory) (a n : Nat) : List Nat :=
  (List.range n).map (fun i => m.read (a + i))

def Memory.load (m : Memory) (a width : Nat) : Nat :=
  ((List.range width).map (fun i => m.read (a+i) * 256^i)).sum

def Memory.store (m : Memory) (a width v : Nat) : Memory :=
  m.writeBytes a ((List.range width).map (fun i => v / 256^i % 256))

inductive Status where
  | running | returned (word : Nat) | trap | unsupported | exhausted
  deriving Repr, DecidableEq

structure State where
  pc : Nat := 0
  stack : List Nat := []
  locals : Array Nat
  labels : List Label := []
  mem : Memory
  accesses : List Access := []
  status : Status := .running

def word (n : Nat) : Nat := n % 4294967296

def unary (s : State) (f : Nat → Nat) : State :=
  match s.stack with
  | x :: xs => {s with stack := f x :: xs}
  | _ => {s with status := .trap}

def binary (s : State) (f : Nat → Nat → Nat) : State :=
  match s.stack with
  | b :: a :: xs => {s with stack := f a b :: xs}
  | _ => {s with status := .trap}

def branch (s : State) (d : Nat) : State :=
  match s.labels[d]? with
  | none => {s with status := .trap}
  | some l =>
    {s with pc := l.target
            stack := s.stack.drop (s.stack.length - l.height)
            labels := s.labels.drop (d + if l.isLoop then 0 else 1)}

def step (code : Array Op) (s : State) : State := Id.run do
  let some op := code[s.pc]? | return {s with status := .trap}
  let t := {s with pc := s.pc + 1}
  match op with
  | .const n => return {t with stack := n :: t.stack}
  | .get i =>
    let some n := t.locals[i]? | return {t with status := .trap}
    return {t with stack := n :: t.stack}
  | .set i | .tee i =>
    let x :: xs := t.stack | return {t with status := .trap}
    if i ≥ t.locals.size then return {t with status := .trap}
    return {t with locals := t.locals.set! i x,
                   stack := if op == .tee i then t.stack else xs}
  | .add => return binary t (fun a b => word (a+b))
  | .sub => return binary t (fun a b => word (a+4294967296-b))
  | .eq => return binary t (fun a b => if a = b then 1 else 0)
  | .ne => return binary t (fun a b => if a ≠ b then 1 else 0)
  | .lt => return binary t (fun a b => if a < b then 1 else 0)
  | .le => return binary t (fun a b => if a ≤ b then 1 else 0)
  | .gt => return binary t (fun a b => if a > b then 1 else 0)
  | .ge => return binary t (fun a b => if a ≥ b then 1 else 0)
  | .eqz => return unary t (fun a => if a = 0 then 1 else 0)
  | .band => return binary t Nat.land
  | .shr => return binary t (fun a b => a / 2^(b%32))
  | .select =>
    let c :: b :: a :: xs := t.stack | return {t with status := .trap}
    return {t with stack := (if c ≠ 0 then a else b) :: xs}
  | .block e =>
    return {t with labels := ⟨e+1, t.stack.length, false⟩ :: t.labels}
  | .loop _ =>
    return {t with labels := ⟨t.pc, t.stack.length, true⟩ :: t.labels}
  | .end =>
    match t.labels with
    | _ :: ls => return {t with labels := ls}
    | [] =>
      let x :: _ := t.stack | return {t with status := .trap}
      return {t with status := .returned x}
  | .br d => return branch t d
  | .brIf d =>
    let c :: xs := t.stack | return {t with status := .trap}
    let t := {t with stack := xs}
    return if c = 0 then t else branch t d
  | .ret =>
    let x :: _ := t.stack | return {t with status := .trap}
    return {t with status := .returned x}
  | .unreachable => return {t with status := .trap}
  | .unsupported _ => return {t with status := .unsupported}
  | .load w off =>
    let a :: xs := t.stack | return {t with status := .trap}
    let a := a + off
    if a + w > 2097152 then return {t with status := .trap}
    return {t with stack := t.mem.load a w :: xs,
                   accesses := ⟨false, a, w⟩ :: t.accesses}
  | .store w off =>
    let v :: a :: xs := t.stack | return {t with status := .trap}
    let a := a + off
    if a + w > 2097152 then return {t with status := .trap}
    return {t with stack := xs, mem := t.mem.store a w v,
                   accesses := ⟨true, a, w⟩ :: t.accesses}
  | .copy =>
    let n :: src :: dst :: xs := t.stack | return {t with status := .trap}
    if src + n > 2097152 ∨ dst + n > 2097152 then
      return {t with status := .trap}
    return {t with stack := xs,
                   mem := t.mem.writeBytes dst (t.mem.readBytes src n),
                   accesses := ⟨true, dst, n⟩ :: ⟨false, src, n⟩ :: t.accesses}
  | .fill =>
    let n :: v :: dst :: xs := t.stack | return {t with status := .trap}
    if dst + n > 2097152 then return {t with status := .trap}
    return {t with stack := xs,
                   mem := t.mem.writeBytes dst (List.replicate n (v%256)),
                   accesses := ⟨true, dst, n⟩ :: t.accesses}

def run (code : Array Op) : Nat → State → State
  | 0, s => if s.status == .running then {s with status := .exhausted} else s
  | fuel+1, s => if s.status == .running then run code fuel (step code s) else s

def inRange (a start len : Nat) : Bool := start ≤ a && a < start+len

/-- Per-byte check, including accesses straddling the boundary of the caller band. -/
def confined (src dst n cap : Nat) (a : Access) : Bool :=
  (List.range a.width).all fun i =>
    let p := a.address+i
    !inRange p 131072 (2097152-131072) ||
      if a.write then inRange p dst cap
      else inRange p src n || inRange p dst cap

end Wasm
