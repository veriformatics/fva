import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/- Executable semantics for the scalar, resultless-block Wasm subset used by
   functions 2, 3 and 4 of the shipped module. Unsupported instructions fail
   closed in the extractor. This is a model, not a verified Wasm implementation. -/
namespace Verification

def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def signed (n : Nat) : Int := if n < 2147483648 then n else (n : Int) - modulus
def bit (b : Bool) : Nat := if b then 1 else 0

inductive Unary where
  | eqz
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | band | bxor | shl | shr
  | eq | ne | ltU | leU | gtU | geU | ltS | gtS
  deriving DecidableEq, Repr

def binary : Binary → Nat → Nat → Nat
  | .add, a, b => word (a + b)
  | .sub, a, b => word (a + modulus - b)
  | .band, a, b => Nat.land a b
  | .bxor, a, b => Nat.xor a b
  | .shl, a, b => word (a * 2 ^ (b % 32))
  | .shr, a, b => a / 2 ^ (b % 32)
  | .eq, a, b => bit (a == b)
  | .ne, a, b => bit (a != b)
  | .ltU, a, b => bit (a < b)
  | .leU, a, b => bit (a ≤ b)
  | .gtU, a, b => bit (a > b)
  | .geU, a, b => bit (a ≥ b)
  | .ltS, a, b => bit (signed a < signed b)
  | .gtS, a, b => bit (signed a > signed b)

inductive Instr where
  | const (n : Nat)
  | get (n : Nat) | set (n : Nat) | tee (n : Nat)
  | unary (op : Unary) | bin (op : Binary)
  | block (body : List Instr) | loop (body : List Instr)
  | br (depth : Nat) | brIf (depth : Nat)
  | call (index : Nat)
  | load (width offset : Nat) | store (width offset : Nat)
  | select | drop | ret
  deriving Repr

structure Func where
  params : Nat
  locals : Nat
  body : List Instr
  deriving Repr

structure Access where
  write : Bool
  addr : Nat
  width : Nat
  deriving DecidableEq, Repr

abbrev Memory := Nat → Nat

structure State where
  stack : List Nat
  locals : List Nat
  mem : Memory
  trace : List Access := [] -- reverse chronological

inductive Result where
  | normal (s : State)
  | branch (depth : Nat) (s : State)
  | returned (s : State)
  | trap | timeout

def memorySize : Nat := 2097152

def readLE (m : Memory) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m addr % 256 + 256 * readLE m (addr + 1) n

def writeLE (m : Memory) (addr value : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => writeLE (fun a => if a = addr then value % 256 else m a)
      (addr + 1) (value / 256) n

def setLocal (s : State) (n v : Nat) : State :=
  { s with locals := s.locals.set n v }

/- Fuel bounds recursion depth. Timeout is never treated as a successful run.
   Calls have one i32 result; blocks and loops have no parameters/results.
   Their branch targets restore the entry operand stack. -/
def eval (module : Nat → Option Func) : Nat → List Instr → State → Result
  | 0, _, _ => .timeout
  | _ + 1, [], s => .normal s
  | fuel + 1, i :: tail, s =>
    let next := eval module fuel tail
    match i with
    | .const n => next { s with stack := word n :: s.stack }
    | .get n => match s.locals[n]? with
      | some v => next { s with stack := v :: s.stack }
      | none => .trap
    | .set n => match s.stack with
      | v :: rest =>
        if n < s.locals.length then
          next { setLocal s n v with stack := rest }
        else .trap
      | _ => .trap
    | .tee n => match s.stack with
      | v :: _ => if n < s.locals.length then next (setLocal s n v) else .trap
      | _ => .trap
    | .unary .eqz => match s.stack with
      | a :: rest => next { s with stack := bit (a == 0) :: rest }
      | _ => .trap
    | .bin op => match s.stack with
      | b :: a :: rest => next { s with stack := binary op a b :: rest }
      | _ => .trap
    | .block body =>
      match eval module fuel body s with
      | .normal t => next t
      | .branch 0 t => next { t with stack := s.stack }
      | .branch (n + 1) t => .branch n t
      | r => r
    | .loop body =>
      match eval module fuel body s with
      | .normal t => next t
      | .branch 0 t => eval module fuel (i :: tail) { t with stack := s.stack }
      | .branch (n + 1) t => .branch n t
      | r => r
    | .br n => .branch n s
    | .brIf n => match s.stack with
      | c :: rest =>
        let t := { s with stack := rest }
        if c = 0 then next t else .branch n t
      | _ => .trap
    | .call n => match module n with
      | none => .trap
      | some f =>
        if s.stack.length < f.params then .trap else
        let args := (s.stack.take f.params).reverse
        let callee := { s with stack := [], locals := args ++ List.replicate f.locals 0 }
        let resume (t : State) := match t.stack with
          | [v] => next { t with stack := v :: s.stack.drop f.params, locals := s.locals }
          | _ => .trap
        match eval module fuel f.body callee with
        | .normal t | .returned t => resume t
        | .branch 0 t => match t.stack with -- implicit function result label
          | v :: _ => next { t with stack := v :: s.stack.drop f.params, locals := s.locals }
          | _ => .trap
        | .timeout => .timeout
        | _ => .trap
    | .load width offset => match s.stack with
      | a :: rest =>
        if a + offset + width ≤ memorySize then
          next { s with stack := readLE s.mem (a + offset) width :: rest, trace := ⟨false, a + offset, width⟩ :: s.trace }
        else .trap
      | _ => .trap
    | .store width offset => match s.stack with
      | v :: a :: rest =>
        if a + offset + width ≤ memorySize then
          next { s with stack := rest, mem := writeLE s.mem (a + offset) v width, trace := ⟨true, a + offset, width⟩ :: s.trace }
        else .trap
      | _ => .trap
    | .select => match s.stack with
      | c :: b :: a :: rest => next { s with stack := (if c = 0 then b else a) :: rest }
      | _ => .trap
    | .drop => match s.stack with
      | _ :: rest => next { s with stack := rest }
      | _ => .trap
    | .ret => .returned s

end Verification
