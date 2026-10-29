import Init

/- A deliberately partial Wasm evaluator. Unsupported instructions, bad stacks,
   exhausted fuel, and out-of-memory accesses return none, never success.
   Blocks in the extracted function all have the empty block type. -/
namespace Wasm

inductive Instr where
  | op (code a b : Nat)
  | block (isLoop : Bool) (body : List Instr)
  deriving Repr, Inhabited

def leb : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b < 128 then some (b, bs) else do
      let (n, rest) ← leb k bs
      pure (b % 128 + 128 * n, rest)

def immediate (op : Nat) (bs : List Nat) : Option (Nat × Nat × List Nat) := do
  if op == 65 then
    let (n, rest) ← leb 5 bs
    -- All i32.const encodings in this function use signed LEB32.
    let used := bs.length - rest.length
    let n := if n / 2^(7*used-1) == 1 then (n + 2^32 - 2^(7*used)) % 2^32 else n
    pure (n, 0, rest)
  else if [12, 13, 16, 32, 33, 34].contains op then
    let (n, rest) ← leb 5 bs
    pure (n, 0, rest)
  else if [40, 41, 45, 47, 54, 55, 58, 59].contains op then
    let (a, rest) ← leb 5 bs
    let (b, rest) ← leb 5 rest
    pure (a, b, rest)
  else if op == 252 then
    let (n, rest) ← leb 5 bs
    match n, rest with
    | 10, 0 :: 0 :: rest => pure (10, 0, rest)
    | 11, 0 :: rest => pure (11, 0, rest)
    | _, _ => none
  else if [0, 15, 27, 69, 70, 71, 73, 75, 77, 79, 106, 107, 113, 118].contains op then
    pure (0, 0, bs)
  else none

def parse : Nat → List Nat → Option (List Instr × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, op :: bs => do
    if op == 11 then pure ([], bs)
    else if op == 2 || op == 3 then
      let 64 :: bs := bs | none
      let (body, rest) ← parse k bs
      let (tail, rest) ← parse k rest
      pure (.block (op == 3) body :: tail, rest)
    else
      let (a, b, rest) ← immediate op bs
      let (tail, rest) ← parse k rest
      pure (.op op a b :: tail, rest)

structure Region where
  src : Nat
  dst : Nat
  n : Nat
  cap : Nat
  deriving Repr

def inside (p len base size : Nat) : Bool := base ≤ p && p + len ≤ base + size

def allowed (r : Region) (write : Bool) (p len : Nat) : Bool :=
  inside p len r.dst r.cap || (!write && inside p len r.src r.n)

structure Mem where
  initial : Nat → Nat
  writes : List (Nat × Nat) := []

def byte (m : Mem) (p : Nat) : Nat :=
  match m.writes.find? (fun x => x.1 == p) with
  | some x => x.2
  | none => m.initial p

def load (m : Mem) (p : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => byte m p + 256 * load m (p + 1) k

def store (m : Mem) (p value : Nat) : Nat → Mem
  | 0 => m
  | k + 1 => store { m with writes := (p, value % 256) :: m.writes } (p+1) (value/256) k

structure Frame where
  loopBody : Option (List Instr)
  afterBody : List Instr
  savedStack : List Nat

structure State where
  todo : List Instr
  frames : List Frame := []
  stack : List Nat := []
  locals : List Nat
  mem : Mem
  region : Region
  reads : List (Nat × Nat) := []
  safe : Bool := true
  result : Option Nat := none

def branch (s : State) (depth : Nat) : Option State := do
  let f ← s.frames[depth]?
  match f.loopBody with
  | some body => pure { s with todo := body, frames := s.frames.drop depth, stack := f.savedStack }
  | none => pure { s with todo := f.afterBody, frames := s.frames.drop (depth+1), stack := f.savedStack }

def bin (op x y : Nat) : Option Nat :=
  match op with
  | 70 => some (if x == y then 1 else 0)
  | 71 => some (if x != y then 1 else 0)
  | 73 => some (if x < y then 1 else 0)
  | 75 => some (if x > y then 1 else 0)
  | 77 => some (if x ≤ y then 1 else 0)
  | 79 => some (if x ≥ y then 1 else 0)
  | 106 => some ((x+y) % 2^32)
  | 107 => some ((x+2^32-y) % 2^32)
  | 113 => some (Nat.land x y)
  | 118 => some (x / 2^(y % 32))
  | _ => none

def step (s : State) : Option State := do
  match s.todo with
  | [] =>
    match s.frames with
    | [] =>
      let [v] := s.stack | none
      pure { s with result := some v }
    | f :: fs =>
      if s.stack.length != f.savedStack.length then none
      else pure { s with todo := f.afterBody, frames := fs }
  | .block loop body :: rest =>
    pure { s with todo := body, frames := ⟨if loop then some body else none, rest, s.stack⟩ :: s.frames }
  | .op op a b :: rest =>
    let s := { s with todo := rest }
    match op with
    | 65 => pure { s with stack := a :: s.stack }
    | 32 => let v ← s.locals[a]?; pure { s with stack := v :: s.stack }
    | 33 | 34 =>
      let v :: vs := s.stack | none
      if a ≥ s.locals.length then none else
        pure { s with locals := s.locals.set a v, stack := if op == 34 then s.stack else vs }
    | 12 => branch s a
    | 13 =>
      let v :: vs := s.stack | none
      let s := { s with stack := vs }
      if v == 0 then pure s else branch s a
    | 15 =>
      let v :: _ := s.stack | none
      pure { s with result := some v }
    | 27 =>
      let c :: y :: x :: vs := s.stack | none
      pure { s with stack := (if c != 0 then x else y) :: vs }
    | 69 =>
      let v :: vs := s.stack | none
      pure { s with stack := (if v == 0 then 1 else 0) :: vs }
    | 40 | 41 | 45 | 47 =>
      let p :: vs := s.stack | none
      let p := p + b
      let len := if op == 40 then 4 else if op == 41 then 8 else if op == 45 then 1 else 2
      if p + len > 2097152 then none else
        pure { s with stack := load s.mem p len :: vs, reads := (p, len) :: s.reads, safe := s.safe && allowed s.region false p len }
    | 54 | 55 | 58 | 59 =>
      let v :: p :: vs := s.stack | none
      let p := p + b
      let len := if op == 54 then 4 else if op == 55 then 8 else if op == 58 then 1 else 2
      if p + len > 2097152 then none else
        pure { s with stack := vs, mem := store s.mem p v len, safe := s.safe && allowed s.region true p len }
    | 252 =>
      let len :: v :: p :: vs := s.stack | none
      if p + len > 2097152 then none else
      if a == 10 then
        if v + len > 2097152 then none else
        let bytes := (List.range len).map (fun i => (p+i, byte s.mem (v+i)))
        pure { s with stack := vs, mem := { s.mem with writes := bytes ++ s.mem.writes }, reads := (v, len) :: s.reads, safe := s.safe && allowed s.region false v len && allowed s.region true p len }
      else if a == 11 then
        let bytes := (List.range len).map (fun i => (p+i, v % 256))
        pure { s with stack := vs, mem := { s.mem with writes := bytes ++ s.mem.writes }, safe := s.safe && allowed s.region true p len }
      else none
    | _ =>
      let y :: x :: vs := s.stack | none
      let v ← bin op x y
      pure { s with stack := v :: vs }

def run : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, s => if s.result.isSome then some s else step s >>= run fuel

def initial (program : List Instr) (r : Region) (m : Nat → Nat) : State :=
  { todo := program, locals := [r.src, r.dst, r.n, r.cap] ++ List.replicate 24 0,
    mem := ⟨m, []⟩, region := r }

end Wasm
