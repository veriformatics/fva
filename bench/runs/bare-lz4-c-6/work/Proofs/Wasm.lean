import Mathlib.Tactic

/- An executable semantics for the integer, zero-arity-control Wasm subset used by
   the decoder and its two callees. Branch labels are resolved by extract.py.
   Values are natural-number representatives of i32; all arithmetic wraps. -/
namespace Wasm

def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def signed (n : Nat) : Int := if n < 2147483648 then n else (n : Int) - modulus

def bool (b : Bool) : Nat := if b then 1 else 0

inductive Bin where
  | add | sub | and | xor | shl | shr_u | eq | ne | lt_u | le_u | gt_u | ge_u | lt_s
  deriving Repr, DecidableEq

inductive Instr where
  | nop | const (v : Nat) | get (n : Nat) | set (n : Nat) | tee (n : Nat)
  | bin (op : Bin) | eqz | select | drop
  | jump (pc : Nat) | jumpIf (pc : Nat)
  | load (width offset : Nat) | store (width offset : Nat)
  | call (fn : Nat) | ret
  deriving Repr, DecidableEq

structure Func where
  params : Nat
  locals : Nat
  code : Nat → Option Instr

abbrev Program := Nat → Option Func

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq

structure Memory where
  initial : Nat → Nat
  writes : List (Nat × Nat) := []

def Memory.get (m : Memory) (a : Nat) : Nat :=
  match m.writes.lookup a with
  | some v => v
  | none => m.initial a % 256

def Memory.put (m : Memory) (a v : Nat) : Memory :=
  { m with writes := (a, v % 256) :: m.writes }

def Memory.load (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m.get a + 256 * m.load (a + 1) n

def Memory.store (m : Memory) (a v : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => (m.put a v).store (a + 1) (v / 256) n

structure Frame where
  fn : Nat
  pc : Nat
  locals : Array Nat
  stack : List Nat

structure State where
  fn : Nat := 2
  pc : Nat := 0
  locals : Array Nat
  stack : List Nat := []
  frames : List Frame := []
  memory : Memory
  accesses : List Access := []
  result : Option Nat := none

def binop (op : Bin) (a b : Nat) : Option Nat :=
  match op with
  | .add => some (word (a + b))
  | .sub => some (word (a + modulus - b))
  | .and => some (Nat.land a b)
  | .xor => some (Nat.xor a b)
  | .shl => some (word (a * 2^(b % 32)))
  | .shr_u => some (a / 2^(b % 32))
  | .eq => some (bool (a == b))
  | .ne => some (bool (a != b))
  | .lt_u => some (bool (a < b))
  | .le_u => some (bool (a ≤ b))
  | .gt_u => some (bool (a > b))
  | .ge_u => some (bool (a ≥ b))
  | .lt_s => some (bool (signed a < signed b))

def fetch (p : Program) (fn pc : Nat) : Option Instr := do
  let f ← p fn
  f.code pc

def step (p : Program) (s : State) : Option State := do
  let op ← fetch p s.fn s.pc
  let s := { s with pc := s.pc + 1 }
  match op with
  | .nop => some s
  | .const v => some { s with stack := v :: s.stack }
  | .get n => do
      let v ← s.locals[n]?
      some { s with stack := v :: s.stack }
  | .set n => do
      let v :: rest := s.stack | none
      if n < s.locals.size then
        some { s with locals := s.locals.set! n v, stack := rest }
      else none
  | .tee n => do
      let v :: _ := s.stack | none
      if n < s.locals.size then some { s with locals := s.locals.set! n v } else none
  | .bin op => do
      let b :: a :: rest := s.stack | none
      let v ← binop op a b
      some { s with stack := v :: rest }
  | .eqz => do
      let a :: rest := s.stack | none
      some { s with stack := bool (a == 0) :: rest }
  | .select => do
      let c :: b :: a :: rest := s.stack | none
      some { s with stack := (if c != 0 then a else b) :: rest }
  | .drop => do
      let _ :: rest := s.stack | none
      some { s with stack := rest }
  | .jump pc => some { s with pc := pc }
  | .jumpIf pc => do
      let c :: rest := s.stack | none
      some { s with pc := if c != 0 then pc else s.pc, stack := rest }
  | .load width offset => do
      let a :: rest := s.stack | none
      let a := a + offset -- memarg addition does NOT wrap in Wasm
      if a + width ≤ 2097152 then
        some { s with stack := s.memory.load a width :: rest,
                      accesses := ⟨false, a, width⟩ :: s.accesses }
      else none
  | .store width offset => do
      let v :: a :: rest := s.stack | none
      let a := a + offset
      if a + width ≤ 2097152 then
        some { s with stack := rest, memory := s.memory.store a v width,
                      accesses := ⟨true, a, width⟩ :: s.accesses }
      else none
  | .call fn => do
      let callee ← p fn
      if s.stack.length < callee.params then none else
        let args := (s.stack.take callee.params).reverse.toArray
        let frame : Frame := ⟨s.fn, s.pc, s.locals, s.stack.drop callee.params⟩
        some { s with fn := fn, pc := 0,
                      locals := args ++ Array.replicate callee.locals 0,
                      stack := [], frames := frame :: s.frames }
  | .ret => do
      let v :: _ := s.stack | none
      match s.frames with
      | [] => some { s with result := some v }
      | f :: rest => some { s with fn := f.fn, pc := f.pc, locals := f.locals, stack := v :: f.stack, frames := rest }

def run : Nat → Program → State → Option State
  | 0, _, _ => none
  | fuel + 1, p, s =>
    if s.result.isSome then some s else
      match step p s with
      | none => none
      | some next => run fuel p next

def initial (src dst size capacity : Nat) (memory : Memory) : State :=
  { locals := #[src, dst, size, capacity] ++ Array.replicate 15 0, memory := memory }

-- R1's access restriction, for every byte of an event (including wide accesses).
def allowed (src size dst capacity : Nat) (e : Access) : Bool :=
  (List.range e.width).all fun i =>
    let a := e.address + i
    a < 131072 || a ≥ 2097152 ||
    ((dst ≤ a && a < dst + capacity) ||
      (!e.write && src ≤ a && a < src + size))

end Wasm
