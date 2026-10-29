import Mathlib.Data.List.Basic

/-!
A small-step, fuel-bounded semantics for the instruction subset of function 7.
Values are unsigned naturals; i32 operations explicitly wrap modulo 2^32.
Unsupported calls and exhaustion are distinct from Wasm traps and returns.
The memory is a total function, but every access checks the fixed Wasm bounds.
-/
namespace Wasm

def word : Nat := 4294967296
def memorySize : Nat := 2097152
abbrev Memory := Nat → Nat

inductive Bin where
  | add | sub | and | shr | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

inductive Instr where
  | const (v : Nat) | get (i : Nat) | set (i : Nat) | tee (i : Nat)
  | bin (op : Bin) | eqz | select
  | block (after : Nat) | loop (after : Nat) | endBlock
  | br (depth : Nat) | brIf (depth : Nat)
  | load (width offset : Nat) | store (width offset : Nat)
  | copy | fill | ret | unreachable | call (index : Nat)
  deriving DecidableEq, Repr

structure Frame where
  target : Nat
  height : Nat
  isLoop : Bool
  deriving Repr

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving DecidableEq, Repr

structure State where
  pc : Nat := 0
  stack : List Nat := []  -- top first
  locals : List Nat
  frames : List Frame := []
  mem : Memory
  accesses : List Access := []  -- newest first

inductive Outcome where
  | next (s : State) | returned (value : Nat) (s : State)
  | trap | unsupported | exhausted

def binEval : Bin → Nat → Nat → Nat
  | .add, a, b => (a + b) % word
  | .sub, a, b => (a + word - b) % word
  | .and, a, b => Nat.land a b
  | .shr, a, b => a / 2 ^ (b % 32)
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a ≠ b then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .gt, a, b => if a > b then 1 else 0
  | .le, a, b => if a ≤ b then 1 else 0
  | .ge, a, b => if a ≥ b then 1 else 0

def readLE (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m a % 256 + 256 * readLE m (a + 1) n

def writeLE (m : Memory) (a value : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => writeLE (fun p => if p = a then value % 256 else m p)
      (a + 1) (value / 256) n

-- memory.copy takes a snapshot, including when its regions overlap.
def copyMemory (m : Memory) (dst src len : Nat) : Memory :=
  fun p => if dst ≤ p ∧ p < dst + len then m (src + (p - dst)) else m p

def fillMemory (m : Memory) (dst value len : Nat) : Memory :=
  fun p => if dst ≤ p ∧ p < dst + len then value % 256 else m p

def branch (s : State) (depth : Nat) : Outcome :=
  match s.frames[depth]? with
  | none => .unsupported
  | some f =>
      .next { s with
        pc := f.target
        stack := s.stack.drop (s.stack.length - f.height)
        frames := s.frames.drop (depth + if f.isLoop then 0 else 1) }

def step (code : Array Instr) (s : State) : Outcome := Id.run do
  let t := { s with pc := s.pc + 1 }
  match code[s.pc]? with
  | none => return .unsupported
  | some (.const v) => return .next { t with stack := v :: s.stack }
  | some (.get i) =>
      match s.locals[i]? with
      | none => return .unsupported
      | some v => return .next { t with stack := v :: s.stack }
  | some (.set i) | some (.tee i) =>
      match s.stack with
      | [] => return .unsupported
      | v :: rest =>
          if i ≥ s.locals.length then return .unsupported
          let keep := match code[s.pc]? with | some (.tee _) => true | _ => false
          return .next { t with
            locals := s.locals.set i v
            stack := if keep then s.stack else rest }
  | some (.bin op) =>
      match s.stack with
      | b :: a :: rest => return .next { t with stack := binEval op a b :: rest }
      | _ => return .unsupported
  | some .eqz =>
      match s.stack with
      | v :: rest => return .next { t with stack := (if v = 0 then 1 else 0) :: rest }
      | _ => return .unsupported
  | some .select =>
      match s.stack with
      | c :: b :: a :: rest =>
          return .next { t with stack := (if c ≠ 0 then a else b) :: rest }
      | _ => return .unsupported
  | some (.block after) =>
      return .next { t with frames := ⟨after, s.stack.length, false⟩ :: s.frames }
  | some (.loop _) =>
      return .next { t with frames := ⟨s.pc + 1, s.stack.length, true⟩ :: s.frames }
  | some .endBlock =>
      match s.frames with
      | _ :: rest => return .next { t with frames := rest }
      | [] =>
          match s.stack with
          | [v] => return .returned v s
          | _ => return .unsupported
  | some (.br depth) => return branch s depth
  | some (.brIf depth) =>
      match s.stack with
      | c :: rest =>
          return if c ≠ 0 then branch { s with stack := rest } depth
            else .next { t with stack := rest }
      | _ => return .unsupported
  | some (.load width offset) =>
      match s.stack with
      | a :: rest =>
          if a + offset + width > memorySize then return .trap
          return .next { t with
            stack := readLE s.mem (a + offset) width :: rest
            accesses := ⟨false, a + offset, width⟩ :: s.accesses }
      | _ => return .unsupported
  | some (.store width offset) =>
      match s.stack with
      | v :: a :: rest =>
          if a + offset + width > memorySize then return .trap
          return .next { t with
            stack := rest
            mem := writeLE s.mem (a + offset) v width
            accesses := ⟨true, a + offset, width⟩ :: s.accesses }
      | _ => return .unsupported
  | some .copy =>
      match s.stack with
      | len :: src :: dst :: rest =>
          if src + len > memorySize ∨ dst + len > memorySize then return .trap
          return .next { t with
            stack := rest
            mem := copyMemory s.mem dst src len
            accesses := ⟨true, dst, len⟩ :: ⟨false, src, len⟩ :: s.accesses }
      | _ => return .unsupported
  | some .fill =>
      match s.stack with
      | len :: v :: dst :: rest =>
          if dst + len > memorySize then return .trap
          return .next { t with
            stack := rest
            mem := fillMemory s.mem dst v len
            accesses := ⟨true, dst, len⟩ :: s.accesses }
      | _ => return .unsupported
  | some .ret =>
      match s.stack with
      | v :: _ => return .returned v s
      | _ => return .unsupported
  | some .unreachable => return .trap
  | some (.call _) => return .unsupported

def run (code : Array Instr) : Nat → State → Outcome
  | 0, _ => .exhausted
  | fuel + 1, s =>
      match step code s with
      | .next t => run code fuel t
      | result => result

def initial (src dst n cap : Nat) (m : Memory) : State :=
  { locals := [src, dst, n, cap] ++ List.replicate 24 0, mem := m }

def within (a width base len : Nat) : Bool :=
  width == 0 || (base ≤ a && a + width ≤ base + len)

def permitted (src dst n cap : Nat) (a : Access) : Bool :=
  -- R1 imposes restrictions only in the caller-address region.
  decide (a.address + a.width ≤ 131072) ||
    if a.write then within a.address a.width dst cap
    else within a.address a.width src n || within a.address a.width dst cap

end Wasm
