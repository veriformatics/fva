import Lean.Elab.Tactic.Omega

namespace Wasm

-- Structured instructions decoded from the binary. Unknown operations block execution.
inductive Ins where
  | op (opcode : Nat) (immediates : List Nat)
  | block (body : List Ins)
  | loop (body : List Ins)
  deriving Repr

abbrev Memory := Nat → Fin 256
structure State where
  locals : List Nat
  stack : List Nat := []
  reads : List Nat := []

inductive Result where
  | normal (s : State)
  | branch (depth : Nat) (s : State)
  | returned (value : Nat) (reads : List Nat)
  | blocked

def word : Nat := 4294967296
def signed (n : Nat) : Int := if n < 2147483648 then n else (n : Int) - word

def binary (op a b : Nat) : Option Nat :=
  match op with
  | 0x47 => some (if a ≠ b then 1 else 0)
  | 0x48 => some (if signed a < signed b then 1 else 0)
  | _ => none

-- Only the instructions needed by the proved paths are interpreted. In particular,
-- every call, every store, and every other opcode BLOCK, never succeed.
def step (m : Memory) (op : Nat) (args : List Nat) (s : State) : Option State := do
  match op, args, s.stack with
  | 0x41, [n], _ => some {s with stack := n :: s.stack}
  | 0x20, [i], _ => do
      let n ← s.locals[i]?
      some {s with stack := n :: s.stack}
  | 0x21, [i], a :: rest =>
      if i < s.locals.length then some {s with locals := s.locals.set i a, stack := rest}
      else none
  | 0x45, [], a :: rest => some {s with stack := (if a = 0 then 1 else 0) :: rest}
  | 0x1b, [], c :: b :: a :: rest =>
      some {s with stack := (if c ≠ 0 then a else b) :: rest}
  | 0x2d, [_, offset], a :: rest =>
      if a + offset < 2097152 then
        some {s with stack := (m (a + offset)).val :: rest, reads := (a + offset) :: s.reads}
      else none
  | _, [], b :: a :: rest => do
      let c ← binary op a b
      some {s with stack := c :: rest}
  | _, _, _ => none

def eval (m : Memory) : Nat → List Ins → State → Result
  | 0, _, _ => .blocked
  | _ + 1, [], s => .normal s
  | fuel + 1, .op 0x0d [d] :: rest, s =>
      match s.stack with
      | [] => .blocked
      | c :: stack => if c = 0 then eval m fuel rest {s with stack}
          else .branch d {s with stack}
  | _ + 1, .op 0x0f [] :: _, s =>
      match s.stack with
      | a :: _ => .returned a s.reads
      | [] => .blocked
  | fuel + 1, .block body :: rest, s =>
      match eval m fuel body s with
      | .normal t | .branch 0 t => eval m fuel rest t
      | .branch (d + 1) t => .branch d t
      | r => r
  | fuel + 1, .op op args :: rest, s =>
      match step m op args s with
      | some t => eval m fuel rest t
      | none => .blocked
  | _, .loop _ :: _, _ => .blocked

def execute (code : List Ins) (m : Memory) (src dst size cap : Nat) : Option (Nat × List Nat) :=
  match eval m 128 code {locals := [src, dst, size, cap] ++ List.replicate 15 0} with
  | .returned n reads => some (n, reads)
  | .normal {stack := n :: _, reads, ..} => some (n, reads)
  | _ => none
end Wasm
