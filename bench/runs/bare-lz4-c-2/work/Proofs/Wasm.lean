import Mathlib.Data.Nat.Bitwise

/- A deliberately small, executable semantics for the integer-only, single-memory
   Wasm subset reachable from this module's decompressor. Values are unsigned i32s;
   operands are top-first. Unsupported instructions are rejected by the extractor.
   No C semantics or compiler-correctness assumption is used. -/
namespace Verification.Wasm

def modulus : Nat := 4294967296
def memorySize : Nat := 2097152
def i32 (n : Nat) : Nat := n % modulus

inductive Bin where
  | add | sub | band | bxor | shl | shr | eq | ne | ltu | leu | gtu | geu | lts
  deriving Repr, DecidableEq

inductive Instr where
  | const (n : Nat) | get (n : Nat) | set (n : Nat) | tee (n : Nat)
  | block (last : Nat) (isLoop : Bool) | end | br (depth : Nat) | brIf (depth : Nat)
  | call (fn : Nat) | ret | drop | select | eqz | bin (op : Bin)
  | load (width offset : Nat) | store (width offset : Nat)
  deriving Repr, DecidableEq

structure Func where
  params : Nat
  locals : Nat
  code : Array Instr
  deriving Repr, DecidableEq

-- A finite map of byte writes over zero-initialized linear memory.
abbrev Memory := List (Nat × Nat)

def byte (m : Memory) (a : Nat) : Nat :=
  match m.find? (fun p => p.1 == a) with
  | some p => p.2 % 256
  | none => 0

def putBytes (m : Memory) (a : Nat) (bs : List Nat) : Memory :=
  (bs.zipIdx.map fun (b, j) => (a + j, b % 256)) ++ m

def readLE (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => byte m a + 256 * readLE m (a + 1) n

def writeLE (m : Memory) (a : Nat) (v : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => writeLE ((a, v % 256) :: m) (a + 1) (v / 256) n

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq

structure Label where
  target : Nat
  height : Nat
  isLoop : Bool
  deriving Repr, DecidableEq

structure Frame where
  fn : Nat
  pc : Nat := 0
  locals : List Nat
  stack : List Nat := []
  labels : List Label := []
  deriving Repr, DecidableEq

structure State where
  frame : Frame
  callers : List Frame := []
  mem : Memory
  accesses : List Access := []
  deriving Repr, DecidableEq

structure Result where
  value : Nat
  mem : Memory
  accesses : List Access
  deriving Repr, DecidableEq

inductive Progress where
  | next (s : State)
  | done (r : Result)

def binary (op : Bin) (a b : Nat) : Nat :=
  match op with
  | .add => i32 (a + b)
  | .sub => i32 (a + modulus - b)
  | .band => Nat.land a b
  | .bxor => Nat.xor a b
  | .shl => i32 (a * 2 ^ (b % 32))
  | .shr => a / 2 ^ (b % 32)
  | .eq => if a = b then 1 else 0
  | .ne => if a ≠ b then 1 else 0
  | .ltu => if a < b then 1 else 0
  | .leu => if a ≤ b then 1 else 0
  | .gtu => if a > b then 1 else 0
  | .geu => if a ≥ b then 1 else 0
  | .lts => if i32 (a + 2147483648) < i32 (b + 2147483648) then 1 else 0

def finish (s : State) : Option Progress := do
  let v ← s.frame.stack.head?
  match s.callers with
  | [] => return .done ⟨v, s.mem, s.accesses⟩
  | f :: fs => return .next {s with frame := {f with stack := v :: f.stack}, callers := fs}

def branch (s : State) (depth : Nat) : Option Progress := do
  let label ← s.frame.labels[depth]?
  let f := s.frame
  if f.stack.length < label.height then none else
    return .next {s with frame := {f with
      pc := label.target
      stack := f.stack.drop (f.stack.length - label.height)
      labels := f.labels.drop (depth + if label.isLoop then 0 else 1)}}

-- none represents a trap, a malformed extracted program, or exhausted fuel.
def step (program : Array Func) (s : State) : Option Progress := do
  let func ← program[s.frame.fn]?
  let ins ← func.code[s.frame.pc]?
  let f := {s.frame with pc := s.frame.pc + 1}
  let s := {s with frame := f}
  match ins with
  | .const v => return .next {s with frame := {f with stack := v :: f.stack}}
  | .get n =>
    let v ← f.locals[n]?
    return .next {s with frame := {f with stack := v :: f.stack}}
  | .set n =>
    let v ← f.stack.head?
    if n ≥ f.locals.length then none else
      return .next {s with frame := {f with locals := f.locals.set n v, stack := f.stack.drop 1}}
  | .tee n =>
    let v ← f.stack.head?
    if n ≥ f.locals.length then none else
      return .next {s with frame := {f with locals := f.locals.set n v}}
  | .block last isLoop =>
    let label := Label.mk (if isLoop then f.pc else last + 1) f.stack.length isLoop
    return .next {s with frame := {f with labels := label :: f.labels}}
  | .end =>
    match f.labels with
    | [] => none
    | _ :: ls => return .next {s with frame := {f with labels := ls}}
  | .br depth => branch s depth
  | .brIf depth =>
    let v ← f.stack.head?
    let s := {s with frame := {f with stack := f.stack.drop 1}}
    if v = 0 then return .next s else branch s depth
  | .call fn =>
    let callee ← program[fn]?
    if f.stack.length < callee.params then none else
      let args := (f.stack.take callee.params).reverse
      let caller := {f with stack := f.stack.drop callee.params}
      return .next {s with frame := ⟨fn, 0, args ++ List.replicate callee.locals 0, [], []⟩, callers := caller :: s.callers}
  | .ret => finish s
  | .drop =>
    let _ ← f.stack.head?
    return .next {s with frame := {f with stack := f.stack.drop 1}}
  | .select =>
    match f.stack with
    | c :: b :: a :: rest =>
      return .next {s with frame := {f with stack := (if c = 0 then b else a) :: rest}}
    | _ => none
  | .eqz =>
    match f.stack with
    | a :: rest => return .next {s with frame := {f with stack := (if a = 0 then 1 else 0) :: rest}}
    | _ => none
  | .bin op =>
    match f.stack with
    | b :: a :: rest => return .next {s with frame := {f with stack := binary op a b :: rest}}
    | _ => none
  | .load width offset =>
    match f.stack with
    | a :: rest =>
      let a := a + offset -- effective addresses do not wrap in Wasm
      if a + width > memorySize then none else
        return .next {s with frame := {f with stack := readLE s.mem a width :: rest}, accesses := ⟨false, a, width⟩ :: s.accesses}
    | _ => none
  | .store width offset =>
    match f.stack with
    | v :: a :: rest =>
      let a := a + offset
      if a + width > memorySize then none else
        return .next {s with frame := {f with stack := rest}, mem := writeLE s.mem a v width, accesses := ⟨true, a, width⟩ :: s.accesses}
    | _ => none

def run (program : Array Func) : Nat → State → Option Result
  | 0, _ => none
  | fuel + 1, s => do
    match ← step program s with
    | .done r => return r
    | .next t => run program fuel t

def initialState (program : Array Func) (fn : Nat) (args : List Nat) (m : Memory) : Option State := do
  let f ← program[fn]?
  if args.length ≠ f.params then none else
    return ⟨⟨fn, 0, args.map i32 ++ List.replicate f.locals 0, [], []⟩, [], m, []⟩

def invoke (program : Array Func) (fuel fn : Nat) (args : List Nat) (m : Memory) : Option Result :=
  initialState program fn args m >>= run program fuel

end Verification.Wasm
