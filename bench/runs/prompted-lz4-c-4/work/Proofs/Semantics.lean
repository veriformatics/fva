/- A deliberately partial, fail-closed semantics for the actual Wasm instructions.
   Only early-return paths are certified. Unsupported instructions return none.
   Integers are unsigned i32 representatives; memory is a total byte function.
   Reads trap outside the shipped module's fixed 32-page memory. -/
namespace Artifact

inductive Instr where
  | op (opcode : Nat) (args : List Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  deriving Repr

abbrev Memory := Nat → Nat

structure State where
  stack : List Nat := []
  locals : List Nat
  memory : Memory
  reads : List Nat := []

inductive Exit where
  | next (s : State)
  | branch (depth : Nat) (s : State)
  | returned (s : State)

def word : Nat := 4294967296
def byte (m : Memory) (a : Nat) : Nat := m a % 256
def signed (n : Nat) : Int :=
  if n < 2147483648 then Int.ofNat n else Int.ofNat n - word
def flag (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def primitive (op : Nat) (args : List Nat) (s : State) : Option Exit := do
  match op, args, s.stack with
  | 65, [n], _ => pure (.next {s with stack := n :: s.stack})
  | 32, [i], _ =>
    let v ← s.locals[i]?
    pure (.next {s with stack := v :: s.stack})
  | 33, [i], v :: vs =>
    if i < s.locals.length then
      pure (.next {s with stack := vs, locals := s.locals.set i v})
    else none
  | 34, [i], v :: _ =>
    if i < s.locals.length then
      pure (.next {s with locals := s.locals.set i v})
    else none
  | 69, [], v :: vs => pure (.next {s with stack := flag (v = 0) :: vs})
  | 71, [], b :: a :: vs => pure (.next {s with stack := flag (a ≠ b) :: vs})
  | 72, [], b :: a :: vs =>
    pure (.next {s with stack := flag (signed a < signed b) :: vs})
  | 13, [d], v :: vs =>
    let t := {s with stack := vs}
    pure (if v = 0 then .next t else .branch d t)
  | 15, [], _ => pure (.returned s)
  | 27, [], c :: b :: a :: vs =>
    pure (.next {s with stack := (if c = 0 then b else a) :: vs})
  | 45, [_, offset], a :: vs =>
    let addr := a + offset
    if addr < 2097152 then
      pure (.next {s with stack := byte s.memory addr :: vs, reads := s.reads ++ [addr]})
    else none
  | _, _, _ => none

-- Fuel bounds nesting and execution; exhaustion is failure, never acceptance.
def run : Nat → List Instr → State → Option Exit
  | 0, _, _ => none
  | _ + 1, [], s => some (.next s)
  | fuel + 1, i :: rest, s => do
    let e ← match i with
      | .op op args => primitive op args s
      | .block body => do
        match ← run fuel body s with
        | .branch 0 t => pure (.next {t with stack := s.stack})
        | .branch (d + 1) t => pure (.branch d t)
        | e => pure e
      | .loop _ => none
    match e with
    | .next t => run fuel rest t
    | e => pure e

def initial (m : Memory) (src dst size cap : Nat) : State :=
  { locals := [src, dst, size, cap] ++ List.replicate 15 0, memory := m }

-- Normal function fall-through and explicit return both require one i32 result.
def finish : Exit → Option (Nat × Memory × List Nat)
  | .next s | .returned s => do
    let [r] := s.stack | none
    pure (r, s.memory, s.reads)
  | .branch _ _ => none

def execute (code : List Instr) (m : Memory) (src dst size cap : Nat) :=
  (run 64 code (initial m src dst size cap)).bind finish

end Artifact
