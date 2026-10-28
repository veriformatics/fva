import Mathlib.Tactic

/- A deliberately small executable semantics for the integer-only Wasm subset
   reachable from this artifact's decoder. All control blocks have type []→[].
   Failures (including exhausted fuel) are none, never successful executions. -/
namespace Verification

inductive Instr where
  | op (opcode immediate : Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  deriving Repr

structure Func where
  params : Nat
  locals : Nat
  body : List Instr

abbrev Memory := List (Nat × Nat)

def readByte (m : Memory) (a : Nat) : Nat :=
  match m with
  | [] => 0
  | (b, v) :: rest => if a = b then v % 256 else readByte rest a

def putBytes (m : Memory) (a : Nat) : List Nat → Memory
  | [] => m
  | b :: bs => putBytes ((a, b % 256) :: m) (a + 1) bs

def readLE (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => readByte m a + 256 * readLE m (a + 1) n

def writeLE (m : Memory) (a v : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => writeLE ((a, v % 256) :: m) (a + 1) (v / 256) n

structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq

structure State where
  stack : List Nat
  locals : List Nat
  memory : Memory
  trace : List Access -- reverse chronological order
  deriving Repr, DecidableEq

inductive Flow where
  | normal (s : State)
  | branch (depth : Nat) (s : State)
  | returned (s : State)
  deriving Repr, DecidableEq

def modulus : Nat := 4294967296
def wrap (v : Nat) : Nat := v % modulus
def boolVal (p : Prop) [Decidable p] : Nat := if p then 1 else 0
def signed (v : Nat) : Int := if v < 2147483648 then v else (v : Int) - modulus

def binary (op x y : Nat) : Option Nat :=
  match op with
  | 0x46 => some (boolVal (x = y))
  | 0x47 => some (boolVal (x ≠ y))
  | 0x48 => some (boolVal (signed x < signed y))
  | 0x49 => some (boolVal (x < y))
  | 0x4a => some (boolVal (signed x > signed y))
  | 0x4b => some (boolVal (x > y))
  | 0x4c => some (boolVal (signed x ≤ signed y))
  | 0x4d => some (boolVal (x ≤ y))
  | 0x4e => some (boolVal (signed x ≥ signed y))
  | 0x4f => some (boolVal (x ≥ y))
  | 0x6a => some (wrap (x + y))
  | 0x6b => some (wrap (x + modulus - y))
  | 0x71 => some (Nat.land x y)
  | 0x72 => some (Nat.lor x y)
  | 0x73 => some (Nat.xor x y)
  | 0x74 => some (wrap (x * 2 ^ (y % 32)))
  | 0x76 => some (x / 2 ^ (y % 32))
  | _ => none

-- Calls and structured control are handled by execute, everything else here.
def simple (op imm : Nat) (s : State) : Option Flow := do
  match op with
  | 0x0c => return .branch imm s
  | 0x0d =>
    let c :: rest := s.stack | none
    let s := {s with stack := rest}
    return if c = 0 then .normal s else .branch imm s
  | 0x0f => return .returned s
  | 0x1a =>
    let _ :: rest := s.stack | none
    return .normal {s with stack := rest}
  | 0x1b =>
    let c :: y :: x :: rest := s.stack | none
    return .normal {s with stack := (if c = 0 then y else x) :: rest}
  | 0x20 =>
    let x ← s.locals[imm]?
    return .normal {s with stack := x :: s.stack}
  | 0x21 | 0x22 =>
    let x :: rest := s.stack | none
    if imm ≥ s.locals.length then none else
      return .normal {s with
        locals := s.locals.set imm x
        stack := if op = 0x22 then s.stack else rest}
  | 0x41 => return .normal {s with stack := imm :: s.stack}
  | 0x45 =>
    let x :: rest := s.stack | none
    return .normal {s with stack := boolVal (x = 0) :: rest}
  | 0x28 | 0x2d | 0x2f =>
    let a :: rest := s.stack | none
    let width := if op = 0x28 then 4 else if op = 0x2d then 1 else 2
    let a := a + imm
    if a + width > 2097152 then none else
      return .normal {s with
        stack := readLE s.memory a width :: rest
        trace := ⟨false, a, width⟩ :: s.trace}
  | 0x36 | 0x3a =>
    let v :: a :: rest := s.stack | none
    let width := if op = 0x36 then 4 else 1
    let a := a + imm
    if a + width > 2097152 then none else
      return .normal {s with
        stack := rest
        memory := writeLE s.memory a v width
        trace := ⟨true, a, width⟩ :: s.trace}
  | _ =>
    let y :: x :: rest := s.stack | none
    let v ← binary op x y
    return .normal {s with stack := v :: rest}

def execute (mod : Nat → Option Func) : Nat → List Instr → State → Option Flow
  | 0, _, _ => none
  | _ + 1, [], s => some (.normal s)
  | fuel + 1, i :: rest, s => do
    let flow ← match i with
      | .op 0x10 idx => do
        let fn ← mod idx
        if s.stack.length < fn.params then none else do
          let args := (s.stack.take fn.params).reverse
          let callee := {s with stack := [], locals := args ++ List.replicate fn.locals 0}
          let flow ← execute mod fuel fn.body callee
          let out ← match flow with
            | .normal t | .returned t => some t
            | .branch _ _ => none
          let [v] := out.stack | none
          pure (.normal {out with
            locals := s.locals
            stack := v :: s.stack.drop fn.params})
      | .op op imm => simple op imm s
      | .block body => do
        let flow ← execute mod fuel body s
        match flow with
        | .branch 0 t => pure (.normal {t with stack := s.stack})
        | .branch (n + 1) t => pure (.branch n t)
        | other => pure other
      | .loop body => do
        let flow ← execute mod fuel body s
        match flow with
        | .branch 0 t => execute mod fuel [i] {t with stack := s.stack}
        | .branch (n + 1) t => pure (.branch n t)
        | other => pure other
    match flow with
    | .normal t => execute mod fuel rest t
    | other => return other

structure Result where
  value : Nat -- unsigned i32 representation; >= 2^31 denotes a negative return
  memory : Memory
  trace : List Access
  deriving Repr, DecidableEq

def invoke (mod : Nat → Option Func) (fuel src dst size capacity : Nat)
    (m : Memory) : Option Result := do
  let fn ← mod 2
  let flow ← execute mod fuel fn.body
    ⟨[], [src, dst, size, capacity] ++ List.replicate fn.locals 0, m, []⟩
  let out ← match flow with
    | .normal t | .returned t => some t
    | .branch _ _ => none
  let [v] := out.stack | none
  return ⟨v, out.memory, out.trace⟩

def legalBuffers (src dst size capacity : Nat) : Prop :=
  131072 ≤ src ∧ src + size ≤ 2097152 ∧
  131072 ≤ dst ∧ dst + capacity ≤ 2097152 ∧
  (src + size ≤ dst ∨ dst + capacity ≤ src)

def safeTrace (src dst size capacity : Nat) (trace : List Access) : Bool :=
  trace.all fun a => (List.range a.width).all fun i =>
    let p := a.address + i
    p < 131072 ||
      (if a.write then dst ≤ p && p < dst + capacity else
        (src ≤ p && p < src + size) || (dst ≤ p && p < dst + capacity))

end Verification
