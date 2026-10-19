/-!
# WebAssembly semantics — FVA trusted base

Subset of WebAssembly 2.0 core: i32/i64 integer numerics, locals, structured control.
Every FVA theorem about compiled code is stated against `Returns`; this file is reviewed
once and shared by every project + source language. Lifted code = `Module` values
produced by `fva lift` from a sha256-pinned `.wasm`.
-/

namespace FVA.Wasm

inductive ValType where
  | i32 | i64
  deriving DecidableEq, Repr

inductive Val where
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)
  deriving DecidableEq, Repr

def Val.type : Val → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64

def ValType.zero : ValType → Val
  | .i32 => .i32 0
  | .i64 => .i64 0

inductive BinOp where
  | add | sub | mul | divS | divU | remS | remU | and | or | xor | shl | shrS | shrU
  deriving DecidableEq, Repr

inductive RelOp where
  | eq | ne | ltS | ltU | gtS | gtU | leS | leU | geS | geU
  deriving DecidableEq, Repr

inductive Instr where
  | unreachable | nop | drop | select
  | localGet (i : Nat) | localSet (i : Nat) | localTee (i : Nat)
  | i32Const (v : BitVec 32) | i64Const (v : BitVec 64)
  | i32Eqz | i64Eqz
  | i32Bin (op : BinOp) | i64Bin (op : BinOp)
  | i32Rel (op : RelOp) | i64Rel (op : RelOp)
  | i32WrapI64 | i64ExtendI32S | i64ExtendI32U
  | block (arity : Nat) (body : List Instr)
  | loop (arity : Nat) (body : List Instr)
  | ite (arity : Nat) (thn els : List Instr)
  | br (depth : Nat) | brIf (depth : Nat) | ret
  deriving Repr

/-- `none` = trap (division by zero, signed overflow). Shift counts taken mod width. -/
def binOp {n : Nat} : BinOp → BitVec n → BitVec n → Option (BitVec n)
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .divU, a, b => if b = 0 then none else some (a / b)
  | .remU, a, b => if b = 0 then none else some (a % b)
  | .divS, a, b => if b = 0 ∨ (a = BitVec.intMin n ∧ b = -1) then none else some (a.sdiv b)
  | .remS, a, b => if b = 0 then none else some (a.srem b)
  | .and, a, b => some (a &&& b)
  | .or, a, b => some (a ||| b)
  | .xor, a, b => some (a ^^^ b)
  | .shl, a, b => some (a <<< (b.toNat % n))
  | .shrU, a, b => some (a >>> (b.toNat % n))
  | .shrS, a, b => some (a.sshiftRight (b.toNat % n))

def relOp {n : Nat} : RelOp → BitVec n → BitVec n → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .ltS, a, b => a.slt b
  | .ltU, a, b => a.ult b
  | .gtS, a, b => b.slt a
  | .gtU, a, b => b.ult a
  | .leS, a, b => a.sle b
  | .leU, a, b => a.ule b
  | .geS, a, b => b.sle a
  | .geU, a, b => b.ule a

def ofBool (b : Bool) : Val := .i32 (if b then 1 else 0)

/-- Operand stack (head = top) + locals (params first). -/
structure St where
  stack : List Val
  locals : List Val

def setLocal (ls : List Val) (i : Nat) (v : Val) : Option (List Val) :=
  if i < ls.length then some (ls.set i v) else none

/-- Non-control instructions; `none` = trap or ill-typed stack. -/
def step : Instr → St → Option St
  | .nop, s => some s
  | .drop, ⟨_ :: st, ls⟩ => some ⟨st, ls⟩
  | .select, ⟨.i32 c :: v2 :: v1 :: st, ls⟩ => some ⟨(if c ≠ 0 then v1 else v2) :: st, ls⟩
  | .localGet i, ⟨st, ls⟩ => ls[i]?.map fun v => ⟨v :: st, ls⟩
  | .localSet i, ⟨v :: st, ls⟩ => (setLocal ls i v).map fun ls' => ⟨st, ls'⟩
  | .localTee i, ⟨v :: st, ls⟩ => (setLocal ls i v).map fun ls' => ⟨v :: st, ls'⟩
  | .i32Const c, ⟨st, ls⟩ => some ⟨.i32 c :: st, ls⟩
  | .i64Const c, ⟨st, ls⟩ => some ⟨.i64 c :: st, ls⟩
  | .i32Eqz, ⟨.i32 a :: st, ls⟩ => some ⟨ofBool (a == 0) :: st, ls⟩
  | .i64Eqz, ⟨.i64 a :: st, ls⟩ => some ⟨ofBool (a == 0) :: st, ls⟩
  | .i32Bin op, ⟨.i32 b :: .i32 a :: st, ls⟩ => (binOp op a b).map fun r => ⟨.i32 r :: st, ls⟩
  | .i64Bin op, ⟨.i64 b :: .i64 a :: st, ls⟩ => (binOp op a b).map fun r => ⟨.i64 r :: st, ls⟩
  | .i32Rel op, ⟨.i32 b :: .i32 a :: st, ls⟩ => some ⟨ofBool (relOp op a b) :: st, ls⟩
  | .i64Rel op, ⟨.i64 b :: .i64 a :: st, ls⟩ => some ⟨ofBool (relOp op a b) :: st, ls⟩
  | .i32WrapI64, ⟨.i64 a :: st, ls⟩ => some ⟨.i32 (a.setWidth 32) :: st, ls⟩
  | .i64ExtendI32U, ⟨.i32 a :: st, ls⟩ => some ⟨.i64 (a.setWidth 64) :: st, ls⟩
  | .i64ExtendI32S, ⟨.i32 a :: st, ls⟩ => some ⟨.i64 (a.signExtend 64) :: st, ls⟩
  | _, _ => none

inductive Outcome where
  | done (s : St)
  | branch (depth : Nat) (s : St)
  | ret (s : St)
  | trap
  | outOfFuel

/-- Structured execution; one fuel unit per instruction. A block body runs on an empty
operand stack; on exit (fall-through or branch to it) its top `arity` values land on the
enclosing stack. A branch to a loop re-enters the loop. -/
def exec : Nat → List Instr → St → Outcome
  | 0, _, _ => .outOfFuel
  | _ + 1, [], s => .done s
  | f + 1, .block n body :: is, s =>
    match exec f body ⟨[], s.locals⟩ with
    | .done s' | .branch 0 s' => exec f is ⟨s'.stack.take n ++ s.stack, s'.locals⟩
    | .branch (d + 1) s' => .branch d s'
    | o => o
  | f + 1, .loop n body :: is, s =>
    match exec f body ⟨[], s.locals⟩ with
    | .done s' => exec f is ⟨s'.stack.take n ++ s.stack, s'.locals⟩
    | .branch 0 s' => exec f (.loop n body :: is) ⟨s.stack, s'.locals⟩
    | .branch (d + 1) s' => .branch d s'
    | o => o
  | f + 1, .ite n t e :: is, ⟨.i32 c :: st, ls⟩ =>
    exec f (.block n (if c ≠ 0 then t else e) :: is) ⟨st, ls⟩
  | _ + 1, .br d :: _, s => .branch d s
  | f + 1, .brIf d :: is, ⟨.i32 c :: st, ls⟩ =>
    if c ≠ 0 then .branch d ⟨st, ls⟩ else exec f is ⟨st, ls⟩
  | _ + 1, .ret :: _, s => .ret s
  | f + 1, i :: is, s =>
    match step i s with
    | some s' => exec f is s'
    | none => .trap

structure Func where
  name : String
  params : List ValType
  locals : List ValType
  results : Nat
  body : List Instr

structure Module where
  funcs : List Func

/-- Results first-to-last; `none` = trap, out of fuel, or argument types ≠ params. -/
def invoke (f : Func) (fuel : Nat) (args : List Val) : Option (List Val) :=
  if args.map Val.type ≠ f.params then none else
  match exec fuel f.body ⟨[], args ++ f.locals.map ValType.zero⟩ with
  | .done s | .ret s | .branch 0 s => some (s.stack.take f.results).reverse
  | _ => none

/-- Exported function `name` of `m`, applied to `args`, terminates without trapping and
returns `res`. -/
def Returns (m : Module) (name : String) (args res : List Val) : Prop :=
  ∃ f ∈ m.funcs.find? (·.name == name), ∃ fuel, invoke f fuel args = some res

end FVA.Wasm
