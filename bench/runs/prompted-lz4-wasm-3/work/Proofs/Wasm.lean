import Init

namespace Verification
-- The validated artifact uses i32 only, empty structured block signatures,
-- byte/word loads and stores, and no imports, tables, globals or indirect calls.
inductive Instr where
  | op (opcode immediate : Nat)
  | block (body : List Instr)
  | loop (body : List Instr)
  | ite (yes no : List Instr)
  deriving Inhabited
structure Fn where
  params : Nat
  results : Nat
  locals : Nat
  body : List Instr
  deriving Inhabited
structure Label where
  body : List Instr
  after : List Instr
  isLoop : Bool
  stack : List Nat
structure Frame where
  todo : List Instr
  labels : List Label
  locals : List Nat
  stack : List Nat
  results : Nat
structure VM extends Frame where
  calls : List Frame := []
  memory : Nat → Nat
  size : Nat
  reads : List Nat := []
  halted : Bool := false
  trapped : Bool := false

def word (n : Nat) : Nat := n % 4294967296
def setLocal (xs : List Nat) (i v : Nat) : List Nat := xs.set i v
def byteAt (m : Nat → Nat) (a v : Nat) : Nat → Nat :=
  fun p => if p = a then v % 256 else m p

def finish (s : VM) : VM :=
  match s.calls with
  | [] => { s with halted := true }
  | f :: fs => { s with toFrame := { f with stack := s.stack.take s.results ++ f.stack },
                         calls := fs }
def branch (s : VM) (n : Nat) : VM :=
  match s.labels[n]? with
  | none => { s with halted := true, trapped := true }
  | some l => { s with todo := (if l.isLoop then l.body else l.after),
                         labels := s.labels.drop (if l.isLoop then n else n+1), stack := l.stack }
def enter (s : VM) (body tail : List Instr) (looping : Bool) : VM :=
  { s with todo := body, labels := ⟨body, tail, looping, s.stack⟩ :: s.labels }
def pop2 (s : VM) (v : Nat) : VM := { s with stack := v :: s.stack.drop 2 }
def bval (b : Bool) : Nat := if b then 1 else 0

def binary (op a b : Nat) : Nat :=
  match op with
  | 70 => bval (a == b)
  | 71 => bval (a != b)
  | 73 => bval (a < b)
  | 74 => bval (word (a+2147483648) > word (b+2147483648))
  | 75 => bval (a > b)
  | 78 => bval (word (a+2147483648) ≥ word (b+2147483648))
  | 79 => bval (a ≥ b)
  | 106 => word (a+b)
  | 107 => word (a+4294967296-b)
  | 108 => word (a*b)
  | 110 => a / b
  | 113 => Nat.land a b
  | 114 => Nat.lor a b
  | 116 => word (Nat.shiftLeft a (b%32))
  | 118 => Nat.shiftRight a (b%32)
  | _ => 0

def load (s : VM) (offset width : Nat) : VM := Id.run do
  let a := s.stack.head! + offset
  let reads := (List.range width).map (a+·) |>.reverse
  if a + width > s.size then
    return { s with halted := true, trapped := true, reads := reads ++ s.reads }
  let v := (List.range width).foldl (fun v i => v + s.memory (a+i) * 256^i) 0
  return { s with stack := v :: s.stack.tail!, reads := reads ++ s.reads }
def store (s : VM) (offset width : Nat) : VM := Id.run do
  let v := s.stack.head!
  let a := s.stack[1]! + offset
  if a + width > s.size then return { s with halted := true, trapped := true }
  let m := (List.range width).foldl (fun m i => byteAt m (a+i) (v / 256^i)) s.memory
  return { s with memory := m, stack := s.stack.drop 2 }

def step (code : List Fn) (s : VM) : VM :=
  match s.todo with
  | [] => match s.labels with
    | [] => finish s
    | l :: ls => { s with todo := l.after, labels := ls }
  | i :: tail =>
    let t := { s with todo := tail }
    match i with
    | .block b => enter t b tail false
    | .loop b => enter t b tail true
    | .ite yes no => enter { t with stack := t.stack.tail! }
                          (if t.stack.head! = 0 then no else yes) tail false
    | .op op imm =>
      match op with
      | 0 => { t with halted := true, trapped := true }
      | 12 => branch t imm
      | 13 => let u := { t with stack := t.stack.tail! }
              if t.stack.head! = 0 then u else branch u imm
      | 15 => finish t
      | 16 => let f := code[imm]!
              { t with todo := f.body, labels := [],
                       locals := (t.stack.take f.params).reverse ++ List.replicate f.locals 0,
                       stack := [], results := f.results,
                       calls := { t.toFrame with stack := t.stack.drop f.params } :: t.calls }
      | 27 => { t with stack := (if t.stack.head! = 0 then t.stack[1]! else t.stack[2]!)
                                 :: t.stack.drop 3 }
      | 32 => { t with stack := t.locals[imm]! :: t.stack }
      | 33 => { t with locals := setLocal t.locals imm t.stack.head!, stack := t.stack.tail! }
      | 34 => { t with locals := setLocal t.locals imm t.stack.head! }
      | 40 => load t imm 4
      | 45 => load t imm 1
      | 54 => store t imm 4
      | 58 => store t imm 1
      | 65 => { t with stack := imm :: t.stack }
      | 69 => { t with stack := bval (t.stack.head! == 0) :: t.stack.tail! }
      | 110 => if t.stack.head! = 0 then { t with halted := true, trapped := true }
               else pop2 t (binary op t.stack[1]! t.stack.head!)
      | 70 | 71 | 73 | 74 | 75 | 78 | 79 | 106 | 107 | 108 | 113 | 114 | 116 | 118 =>
        pop2 t (binary op t.stack[1]! t.stack.head!)
      | _ => { t with halted := true, trapped := true }

def run : Nat → List Fn → VM → VM
  | 0, _, s => s
  | fuel+1, code, s => if s.halted then s else run fuel code (step code s)
def start (code : List Fn) (idx : Nat) (args : List Nat) (m : Nat → Nat) (size : Nat) : VM :=
  let f := code[idx]!
  { todo := f.body, labels := [], locals := args ++ List.replicate f.locals 0,
    stack := [], results := f.results, memory := m, size := size }
end Verification
