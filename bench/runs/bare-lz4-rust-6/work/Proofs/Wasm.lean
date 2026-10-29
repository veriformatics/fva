import Mathlib.Tactic

/-! An executable model of the instruction subset used by function 7.
This is a model, not a proved implementation of the WebAssembly specification.
Calls deliberately stop as `unsupported`: they are never silently assumed safe.
All block types in this function are empty, and all branch labels have arity zero.
-/
namespace Verification

inductive Instr where
  | block | loop | end | unreachable | ret | select
  | br (depth : Nat) | brIf (depth : Nat) | call (index : Nat)
  | get (index : Nat) | set (index : Nat) | tee (index : Nat)
  | const (value : Nat)
  | eqz | eq | ne | lt | gt | le | ge | add | sub | and | shr
  | load (width offset : Nat) | store (width offset : Nat)
  | copy | fill
  deriving Repr, DecidableEq

-- The second component records the last byte, for signed LEB decoding.
def leb : Nat → List Nat → Option (Nat × Nat × List Nat)
  | 0, _ => none
  | _, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, b, bs) else do
      let (v, last, rest) ← leb fuel bs
      pure (b % 128 + 128 * v, last, rest)

def immediate (ctor : Nat → Instr) (bs : List Nat) : Option (Instr × List Nat) := do
  let (n, _, rest) ← leb 5 bs
  pure (ctor n, rest)

def memarg (ctor : Nat → Nat → Instr) (width : Nat) (bs : List Nat) :
    Option (Instr × List Nat) := do
  let (_, _, bs) ← leb 5 bs
  let (offset, _, rest) ← leb 5 bs
  pure (ctor width offset, rest)

def decodeOne : List Nat → Option (Instr × List Nat)
  | [] => none
  | op :: bs =>
    match op with
    | 0x00 => some (.unreachable, bs)
    | 0x02 => match bs with | 0x40 :: rest => some (.block, rest) | _ => none
    | 0x03 => match bs with | 0x40 :: rest => some (.loop, rest) | _ => none
    | 0x0b => some (.end, bs)
    | 0x0c => immediate .br bs
    | 0x0d => immediate .brIf bs
    | 0x0f => some (.ret, bs)
    | 0x10 => immediate .call bs
    | 0x1b => some (.select, bs)
    | 0x20 => immediate .get bs
    | 0x21 => immediate .set bs
    | 0x22 => immediate .tee bs
    | 0x28 => memarg .load 4 bs
    | 0x29 => memarg .load 8 bs
    | 0x2d => memarg .load 1 bs
    | 0x2f => memarg .load 2 bs
    | 0x36 => memarg .store 4 bs
    | 0x37 => memarg .store 8 bs
    | 0x3a => memarg .store 1 bs
    | 0x3b => memarg .store 2 bs
    | 0x41 => do
      let (v, last, rest) ← leb 5 bs
      -- Signed LEB length is the number of bytes consumed.
      let bits := 7 * (bs.length - rest.length)
      let signed : Int := if last < 64 then v else (v : Int) - (2 : Int)^bits
      pure (.const (signed % 4294967296).toNat, rest)
    | 0x45 => some (.eqz, bs)
    | 0x46 => some (.eq, bs)
    | 0x47 => some (.ne, bs)
    | 0x49 => some (.lt, bs)
    | 0x4b => some (.gt, bs)
    | 0x4d => some (.le, bs)
    | 0x4f => some (.ge, bs)
    | 0x6a => some (.add, bs)
    | 0x6b => some (.sub, bs)
    | 0x71 => some (.and, bs)
    | 0x76 => some (.shr, bs)
    | 0xfc => match bs with
      | 10 :: 0 :: 0 :: rest => some (.copy, rest)
      | 11 :: 0 :: rest => some (.fill, rest)
      | _ => none
    | _ => none

def decode : Nat → List Nat → Option (List Instr)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bs => do
    let (i, rest) ← decodeOne bs
    let tail ← decode fuel rest
    pure (i :: tail)

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq

structure Memory where
  initial : Nat → Nat
  writes : List (Nat × Nat) := []

def Memory.byte (m : Memory) (a : Nat) : Nat :=
  match m.writes.find? (fun p => p.1 == a) with
  | some p => p.2
  | none => m.initial a % 256

def Memory.put (m : Memory) (a v : Nat) : Memory :=
  {m with writes := (a, v % 256) :: m.writes}

def Memory.load (m : Memory) (a width : Nat) : Nat :=
  ((List.range width).map (fun i => m.byte (a + i) * 256^i)).sum

def Memory.store (m : Memory) (a width v : Nat) : Memory :=
  (List.range width).foldl (fun m i => m.put (a + i) (v / 256^i)) m

def Memory.copy (m : Memory) (dst src len : Nat) : Memory :=
  (List.range len).foldl (fun out i => out.put (dst + i) (m.byte (src + i))) m

def Memory.fill (m : Memory) (dst val len : Nat) : Memory :=
  (List.range len).foldl (fun out i => out.put (dst + i) val) m

structure Label where
  target : Nat
  isLoop : Bool
  height : Nat
  deriving Repr, DecidableEq

structure State where
  pc : Nat := 0
  stack : List Nat := []
  locals : Array Nat
  labels : List Label := []
  mem : Memory
  accesses : List Access := []

inductive Outcome where
  | running (s : State)
  | returned (r : Nat) (s : State)
  | trap (s : State)
  | unsupported (s : State)
  | exhausted (s : State)

def findEnd (code : Array Instr) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, pc, depth => do
    let instr ← code[pc]?
    match instr with
    | .block | .loop => findEnd code fuel (pc + 1) (depth + 1)
    | .end => if depth == 0 then some pc else findEnd code fuel (pc + 1) (depth - 1)
    | _ => findEnd code fuel (pc + 1) depth

def jump (s : State) (depth : Nat) : Outcome :=
  match s.labels[depth]? with
  | none => .unsupported s
  | some l =>
    if l.height ≤ s.stack.length then
      .running {s with pc := l.target, stack := s.stack.drop (s.stack.length - l.height), labels := s.labels.drop (depth + if l.isLoop then 0 else 1)}
    else .unsupported s

def bin (s : State) (f : Nat → Nat → Nat) : Outcome :=
  match s.stack with
  | b :: a :: rest => .running {s with pc := s.pc + 1, stack := f a b :: rest}
  | _ => .unsupported s

def inMemory (addr len : Nat) : Bool := addr + len ≤ 2097152

def step (code : Array Instr) (s : State) : Outcome :=
  match code[s.pc]? with
  | none => .unsupported s
  | some i =>
    let next := {s with pc := s.pc + 1}
    match i with
    | .unreachable => .trap s
    | .call _ => .unsupported s
    | .block | .loop =>
      match findEnd code code.size (s.pc + 1) 0 with
      | none => .unsupported s
      | some endPc => .running {next with labels :=
          ⟨if i == .loop then s.pc + 1 else endPc + 1, i == .loop, s.stack.length⟩ :: s.labels}
    | .end =>
      match s.labels with
      | l :: ls =>
        if s.stack.length == l.height then .running {next with labels := ls}
        else .unsupported s
      | [] => match s.stack with
        | [r] => .returned r s
        | _ => .unsupported s
    | .ret => match s.stack with
      | r :: _ => .returned r s
      | _ => .unsupported s
    | .br depth => jump s depth
    | .brIf depth => match s.stack with
      | cond :: rest => if cond == 0 then .running {next with stack := rest}
                       else jump {s with stack := rest} depth
      | _ => .unsupported s
    | .get index => match s.locals[index]? with
      | some v => .running {next with stack := v :: s.stack}
      | none => .unsupported s
    | .set index | .tee index => match s.stack with
      | v :: rest =>
        if index < s.locals.size then .running {next with
          locals := s.locals.set! index v, stack := if i == .tee index then s.stack else rest}
        else .unsupported s
      | _ => .unsupported s
    | .const v => .running {next with stack := v :: s.stack}
    | .select => match s.stack with
      | cond :: b :: a :: rest =>
        .running {next with stack := (if cond == 0 then b else a) :: rest}
      | _ => .unsupported s
    | .eqz => match s.stack with
      | v :: rest => .running {next with stack := (if v == 0 then 1 else 0) :: rest}
      | _ => .unsupported s
    | .eq => bin s (fun a b => if a == b then 1 else 0)
    | .ne => bin s (fun a b => if a != b then 1 else 0)
    | .lt => bin s (fun a b => if a < b then 1 else 0)
    | .gt => bin s (fun a b => if a > b then 1 else 0)
    | .le => bin s (fun a b => if a ≤ b then 1 else 0)
    | .ge => bin s (fun a b => if a ≥ b then 1 else 0)
    | .add => bin s (fun a b => (a + b) % 4294967296)
    | .sub => bin s (fun a b => (a + 4294967296 - b) % 4294967296)
    | .and => bin s Nat.land
    | .shr => bin s (fun a b => a / 2^(b % 32))
    | .load width offset => match s.stack with
      | addr :: rest =>
        let a := addr + offset
        if inMemory a width then .running {next with stack := s.mem.load a width :: rest, accesses := ⟨false, a, width⟩ :: s.accesses}
        else .trap s
      | _ => .unsupported s
    | .store width offset => match s.stack with
      | val :: addr :: rest =>
        let a := addr + offset
        if inMemory a width then .running {next with stack := rest, mem := s.mem.store a width val, accesses := ⟨true, a, width⟩ :: s.accesses}
        else .trap s
      | _ => .unsupported s
    | .copy => match s.stack with
      | len :: src :: dst :: rest =>
        if inMemory src len && inMemory dst len then .running {next with stack := rest, mem := s.mem.copy dst src len, accesses := ⟨true, dst, len⟩ :: ⟨false, src, len⟩ :: s.accesses}
        else .trap s
      | _ => .unsupported s
    | .fill => match s.stack with
      | len :: val :: dst :: rest =>
        if inMemory dst len then .running {next with stack := rest, mem := s.mem.fill dst val len, accesses := ⟨true, dst, len⟩ :: s.accesses}
        else .trap s
      | _ => .unsupported s

def run (code : Array Instr) : Nat → State → Outcome
  | 0, s => .exhausted s
  | fuel + 1, s => match step code s with
    | .running next => run code fuel next
    | other => other

end Verification
