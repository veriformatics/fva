import Proofs.Artifact

/- A deliberately partial Wasm interpreter. Unsupported instructions, malformed
   encodings, traps and exhausted fuel return none; they never count as success.
   The artifact's decoder and its two callees use only the supported subset. -/
namespace Wasm

def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def signed (n : Nat) : Int := if n < 2147483648 then n else (n : Int) - modulus

def leb : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, bs) else do
      let (n, rest) ← leb fuel bs
      pure (b % 128 + 128 * n, rest)

def sleb : Nat → List Nat → Option (Int × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (if b < 64 then (b : Int) else (b : Int) - 128, bs)
    else do
      let (n, rest) ← sleb fuel bs
      pure ((b % 128 : Nat) + 128 * n, rest)

inductive Instr where
  | op (opcode a b : Nat)
  | block (isLoop : Bool) (body : List Instr)
  deriving Repr

def instruction (op : Nat) (bs : List Nat) : Option (Instr × List Nat) := do
  if op == 65 then
    let (n, rest) ← sleb 5 bs
    pure (Instr.op op (n % (modulus : Int)).toNat 0, rest)
  else if [12, 13, 16, 32, 33, 34].contains op then
    let (n, rest) ← leb 5 bs
    pure (Instr.op op n 0, rest)
  else if [40, 45, 47, 54, 58].contains op then
    let (alignment, rest) ← leb 5 bs
    let (offset, rest) ← leb 5 rest
    pure (Instr.op op alignment offset, rest)
  else if [15, 26, 27, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79,
           106, 107, 113, 115, 116, 118].contains op then
    pure (Instr.op op 0 0, bs)
  else none

/- Tail recursion avoids repeatedly reparsing nested blocks during reduction. -/
def parseAux : Nat → List Nat → List Instr → List (Bool × List Instr) →
    Option (List Instr × List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, op :: bs, acc, frames => do
    if op == 11 then
      match frames with
      | [] => return (acc.reverse, bs)
      | (loop, outer) :: frames =>
        parseAux fuel bs (.block loop acc.reverse :: outer) frames
    else if op == 2 || op == 3 then
      let 64 :: tail := bs | none
      parseAux fuel tail [] ((op == 3, acc) :: frames)
    else
      let (instr, rest) ← instruction op bs
      parseAux fuel rest (instr :: acc) frames

def parse (fuel : Nat) (bytes : List Nat) : Option (List Instr × List Nat) :=
  parseAux fuel bytes [] []

structure Func where
  arity : Nat
  locals : Nat
  code : List Instr
  deriving Repr

def decode (arity locals : Nat) (bytes : List Nat) : Option Func := do
  let (code, []) ← parse 2000 bytes | none
  pure ⟨arity, locals, code⟩

def program (idx : Nat) : Option Func :=
  match idx with
  | 2 => decode Artifact.arity2 Artifact.locals2 Artifact.bytes2
  | 3 => decode Artifact.arity3 Artifact.locals3 Artifact.bytes3
  | 4 => decode Artifact.arity4 Artifact.locals4 Artifact.bytes4
  | _ => none

abbrev Memory := Nat → Nat
structure Access where
  write : Bool
  addr : Nat
  size : Nat
  deriving DecidableEq, Repr
structure State where
  locals : List Nat
  stack : List Nat
  mem : Memory
  accesses : List Access

inductive Signal where
  | normal | branch (depth : Nat) | ret
  deriving DecidableEq, Repr

def readLE (mem : Memory) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mem addr % 256 + 256 * readLE mem (addr + 1) n

def put (mem : Memory) (addr value : Nat) : Memory :=
  fun x => if x == addr then value % 256 else mem x

def writeLE (mem : Memory) (addr value : Nat) : Nat → Memory
  | 0 => mem
  | n + 1 => writeLE (put mem addr value) (addr + 1) (value / 256) n

def binary (op x y : Nat) : Option Nat :=
  match op with
  | 70 => some (if x == y then 1 else 0)
  | 71 => some (if x != y then 1 else 0)
  | 72 => some (if signed x < signed y then 1 else 0)
  | 73 => some (if x < y then 1 else 0)
  | 74 => some (if signed x > signed y then 1 else 0)
  | 75 => some (if x > y then 1 else 0)
  | 76 => some (if signed x ≤ signed y then 1 else 0)
  | 77 => some (if x ≤ y then 1 else 0)
  | 79 => some (if x ≥ y then 1 else 0)
  | 106 => some (word (x + y))
  | 107 => some (word (x + modulus - y))
  | 113 => some (Nat.land x y)
  | 115 => some (Nat.xor x y)
  | 116 => some (word (x * 2 ^ (y % 32)))
  | 118 => some (x / 2 ^ (y % 32))
  | _ => none

/- The operand stack has its top at the head. All nested block types here are
   empty; functions have one i32 result. The Wasm validator checks typing. -/
def exec : Nat → List Instr → State → Option (Signal × State)
  | 0, _, _ => none
  | _ + 1, [], s => some (.normal, s)
  | fuel + 1, ins :: tail, s => do
    match ins with
    | .block loop body =>
      let (sig, t) ← exec fuel body s
      match sig with
      | .normal => exec fuel tail t
      | .ret => pure (.ret, t)
      | .branch 0 =>
        let t := {t with stack := s.stack}
        if loop then exec fuel (ins :: tail) t else exec fuel tail t
      | .branch (n + 1) => pure (.branch n, t)
    | .op op a b =>
      match op with
      | 12 => pure (.branch a, s)
      | 13 =>
        let c :: stack := s.stack | none
        if c == 0 then exec fuel tail {s with stack}
        else pure (.branch a, {s with stack})
      | 15 => pure (.ret, s)
      | 16 =>
        let f ← program a
        if s.stack.length < f.arity then none else do
          let args := (s.stack.take f.arity).reverse
          let (sig, t) ← exec fuel f.code
            {s with locals := args ++ List.replicate f.locals 0, stack := []}
          if sig != .normal && sig != .ret && sig != .branch 0 then none else do
            let v :: _ := t.stack | none
            exec fuel tail {t with locals := s.locals, stack := v :: s.stack.drop f.arity}
      | 26 =>
        let _ :: stack := s.stack | none
        exec fuel tail {s with stack}
      | 27 =>
        let c :: v2 :: v1 :: stack := s.stack | none
        exec fuel tail {s with stack := (if c == 0 then v2 else v1) :: stack}
      | 32 =>
        let v ← s.locals[a]?
        exec fuel tail {s with stack := v :: s.stack}
      | 33 | 34 =>
        let v :: stack := s.stack | none
        if a ≥ s.locals.length then none else
          exec fuel tail {s with locals := s.locals.set a v, stack := if op == 34 then s.stack else stack}
      | 65 => exec fuel tail {s with stack := a :: s.stack}
      | 69 =>
        let v :: stack := s.stack | none
        exec fuel tail {s with stack := (if v == 0 then 1 else 0) :: stack}
      | 40 | 45 | 47 =>
        let addr :: stack := s.stack | none
        let addr := addr + b
        let size := if op == 40 then 4 else if op == 47 then 2 else 1
        if addr + size > 2097152 then none else
          exec fuel tail {s with stack := readLE s.mem addr size :: stack, accesses := ⟨false, addr, size⟩ :: s.accesses}
      | 54 | 58 =>
        let value :: addr :: stack := s.stack | none
        let addr := addr + b
        let size := if op == 54 then 4 else 1
        if addr + size > 2097152 then none else
          exec fuel tail {s with stack, mem := writeLE s.mem addr value size, accesses := ⟨true, addr, size⟩ :: s.accesses}
      | _ =>
        let y :: x :: stack := s.stack | none
        let v ← binary op x y
        exec fuel tail {s with stack := v :: stack}

def invoke (fuel src dst srcSize capacity : Nat) (mem : Memory) : Option State := do
  let f ← program 2
  let (sig, s) ← exec fuel f.code
    ⟨[src, dst, srcSize, capacity] ++ List.replicate f.locals 0, [], mem, []⟩
  if sig == .normal || sig == .ret || sig == .branch 0 then
    match s.stack with
    | [v] => pure {s with stack := [v]}
    | _ => none
  else none

end Wasm
