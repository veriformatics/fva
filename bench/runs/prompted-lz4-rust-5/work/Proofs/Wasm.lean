import Init

/- A small operational semantics for the integer/control/memory subset used by
   the exported decoder. Unsupported execution is distinct from return/trap.
   The binary is validated separately; all its blocks have empty signatures.
   Memory addresses are unbounded natural numbers until the explicit 2 MiB
   bound check. Values on the operand stack are unsigned bit patterns. -/
namespace Wasm
inductive Bin where
  | eq | ne | lt | gt | le | ge | add | sub | band | shr
  deriving DecidableEq, Repr
inductive Instr where
  | block (afterEnd : Nat) | loop (afterEnd : Nat) | «end»
  | br (depth : Nat) | brIf (depth : Nat) | call (index : Nat)
  | get (index : Nat) | set (index : Nat) | tee (index : Nat)
  | const (value : Nat) | bin (op : Bin) | eqz | select
  | load (width offset : Nat) | store (width offset : Nat)
  | copy | fill | ret | trap
  deriving DecidableEq, Repr
inductive Status where
  | running | returned (bits : Nat) | trapped | unsupported | exhausted
  deriving DecidableEq, Repr
structure Frame where
  target : Nat
  isLoop : Bool
  saved : List Nat
  deriving Repr
structure Event where
  write : Bool
  address : Nat
  length : Nat
  deriving DecidableEq, Repr
abbrev Memory := Nat → Nat
structure State where
  pc : Nat := 0
  stack : List Nat := []
  locals : List Nat
  frames : List Frame := []
  mem : Memory
  events : List Event := []
  status : Status := .running

def modulus : Nat := 4294967296
def w32 (n : Nat) : Nat := n % modulus
def evalBin : Bin → Nat → Nat → Nat
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a ≠ b then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .gt, a, b => if a > b then 1 else 0
  | .le, a, b => if a ≤ b then 1 else 0
  | .ge, a, b => if a ≥ b then 1 else 0
  | .add, a, b => w32 (a + b)
  | .sub, a, b => w32 (a + modulus - b)
  | .band, a, b => Nat.land a b
  | .shr, a, b => a / 2 ^ (b % 32)
def readLE (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m a % 256 + 256 * readLE m (a+1) n
def writeLE (m : Memory) (a v : Nat) : Nat → Memory
  | 0 => m
  | n+1 => writeLE (fun p => if p = a then v % 256 else m p) (a+1) (v/256) n
def copyBytes (original : Memory) (dst src : Nat) : Nat → Memory → Memory
  | 0, m => m
  | n+1, m => copyBytes original (dst+1) (src+1) n
      (fun p => if p = dst then original src % 256 else m p)
def fillBytes (dst value : Nat) : Nat → Memory → Memory
  | 0, m => m
  | n+1, m => fillBytes (dst+1) value n
      (fun p => if p = dst then value % 256 else m p)
def jump (s : State) (d : Nat) : State :=
  match s.frames[d]? with
  | none => { s with status := .unsupported }
  | some f => { s with pc := f.target, stack := f.saved, frames := s.frames.drop (d + if f.isLoop then 0 else 1) }
def step (code : Nat → Option Instr) (s : State) : State := Id.run do
  if s.status != .running then return s
  let bad := { s with status := .unsupported }
  let next := { s with pc := s.pc + 1 }
  match code s.pc with
  | none => return bad
  | some ins =>
    match ins with
    | .block e => return { next with frames := ⟨e, false, s.stack⟩ :: s.frames }
    | .loop _ => return { next with frames := ⟨s.pc+1, true, s.stack⟩ :: s.frames }
    | .end =>
      match s.frames with
      | [] => return bad
      | _ :: fs => return { next with frames := fs }
    | .br d => return jump s d
    | .brIf d =>
      match s.stack with
      | v :: vs =>
        let t := { next with stack := vs }
        return if v = 0 then t else jump t d
      | _ => return bad
    | .get i =>
      match s.locals[i]? with
      | some v => return { next with stack := v :: s.stack }
      | none => return bad
    | .set i | .tee i =>
      match s.stack with
      | v :: vs =>
        if i < s.locals.length then
          return { next with locals := s.locals.set i v, stack := if ins == .tee i then s.stack else vs }
        else return bad
      | _ => return bad
    | .const v => return { next with stack := v :: s.stack }
    | .bin op =>
      match s.stack with
      | b :: a :: vs => return { next with stack := evalBin op a b :: vs }
      | _ => return bad
    | .eqz =>
      match s.stack with
      | a :: vs => return { next with stack := (if a = 0 then 1 else 0) :: vs }
      | _ => return bad
    | .select =>
      match s.stack with
      | c :: b :: a :: vs => return { next with stack := (if c = 0 then b else a) :: vs }
      | _ => return bad
    | .load width offset =>
      match s.stack with
      | a :: vs =>
        let address := a + offset
        if address + width ≤ 2097152 then
          return { next with stack := readLE s.mem address width :: vs, events := ⟨false, address, width⟩ :: s.events }
        else return { s with status := .trapped }
      | _ => return bad
    | .store width offset =>
      match s.stack with
      | v :: a :: vs =>
        let address := a + offset
        if address + width ≤ 2097152 then
          return { next with stack := vs, mem := writeLE s.mem address v width, events := ⟨true, address, width⟩ :: s.events }
        else return { s with status := .trapped }
      | _ => return bad
    | .copy =>
      match s.stack with
      | n :: src :: dst :: vs =>
        if src+n ≤ 2097152 ∧ dst+n ≤ 2097152 then
          return { next with stack := vs, mem := copyBytes s.mem dst src n s.mem, events := ⟨true,dst,n⟩ :: ⟨false,src,n⟩ :: s.events }
        else return { s with status := .trapped }
      | _ => return bad
    | .fill =>
      match s.stack with
      | n :: v :: dst :: vs =>
        if dst+n ≤ 2097152 then
          return { next with stack := vs, mem := fillBytes dst v n s.mem, events := ⟨true,dst,n⟩ :: s.events }
        else return { s with status := .trapped }
      | _ => return bad
    | .ret =>
      match s.stack with
      | v :: _ => return { s with status := .returned v }
      | _ => return bad
    | .trap => return { s with status := .trapped }
    | .call _ => return bad

def run (code : Nat → Option Instr) : Nat → State → State
  | 0, s => s
  | n+1, s => match s.status with
    | .running => run code n (step code s)
    | _ => s

theorem run_stopped (code : Nat → Option Instr) (n : Nat) (s : State)
    (h : s.status ≠ .running) : run code n s = s := by
  cases n with
  | zero => rfl
  | succ n => cases hs : s.status <;> simp_all [run]

theorem run_add (code : Nat → Option Instr) (n k : Nat) (s : State) :
    run code (n+k) s = run code k (run code n s) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    cases hs : s.status <;>
      simp_all [Nat.succ_add, run, run_stopped]

theorem run_join (code : Nat → Option Instr) (n k : Nat) (a b c : State)
    (h₁ : run code n a = b) (h₂ : run code k b = c) :
    run code (n+k) a = c := by
  rw [run_add, h₁, h₂]

def initial (localCount src dst n cap : Nat) (mem : Memory) : State :=
  { locals := [src, dst, n, cap] ++ List.replicate localCount 0, mem := mem }
def bytesAt (m : Memory) (a n : Nat) : List Nat :=
  (List.range n).map (fun i => m (a+i))
def inside (a n base len : Nat) : Bool := base ≤ a && a+n ≤ base+len
/-- The R1 address restriction, including bytes beyond the returned length. -/
def eventSafe (src dst n cap : Nat) (e : Event) : Bool :=
  if e.length = 0 then true else
  if e.address + e.length ≤ 131072 then true else
  if e.write then inside e.address e.length dst cap
  else inside e.address e.length src n || inside e.address e.length dst cap

def memoryOf (src : Nat) (input : List Nat) : Memory := fun a =>
  if src ≤ a then (input[a-src]?).getD 0 else 0
end Wasm
