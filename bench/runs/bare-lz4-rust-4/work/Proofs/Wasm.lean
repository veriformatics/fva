import Proofs.Artifact

/-!
A deliberately partial executable semantics for the integer instructions used by
function 7. Unsupported instructions, calls, malformed stacks, memory traps and
fuel exhaustion all return `none`, never a successful execution. Values are
unsigned natural representatives. Blocks in this function have empty signatures;
the label stack records the operand stack height at entry.

This is a model of Wasm, not a proved implementation of the official semantics.
-/
namespace LZ4Verification

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Reader where
  bytes : List Nat
  pos : Nat := 0
  deriving Repr

def byte (r : Reader) : Option (Nat × Reader) :=
  match r.bytes with
  | [] => none
  | b :: bs => some (b, ⟨bs, r.pos + 1⟩)

def varint : Nat → Nat → Nat → Reader → Option (Nat × Nat × Nat × Reader)
  | 0, _, _, _ => none
  | fuel + 1, acc, shift, r => do
    let (b, r) ← byte r
    let v := acc + (b % 128) * 2^shift
    if b < 128 then return (v, shift + 7, b, r)
    else varint fuel v (shift + 7) r

def uleb (r : Reader) : Option (Nat × Reader) := do
  let (v, _, _, r) ← varint 5 0 0 r
  return (v, r)

def sleb (bits : Nat) (r : Reader) : Option (Nat × Reader) := do
  let (v, shift, last, r) ← varint 10 0 0 r
  let v : Int := if last ≥ 64 then (v : Int) - (2^shift : Nat) else v
  return ((v % (2^bits : Nat)).toNat, r)

/-- List slicing avoids the quadratic logical reduction of repeated Array.push. -/
def slice {α : Type} (bs : Array α) (start stop : Nat) : Array α :=
  ((bs.toList.drop start).take (stop-start)).toArray

def sections : Nat → Reader → Option (List (Nat × Array Nat))
  | 0, _ => none
  | fuel + 1, r => do
    if r.bytes.isEmpty then return []
    let (id, r) ← byte r
    let (len, r) ← uleb r
    if len > r.bytes.length then none else do
      let rest ← sections fuel ⟨r.bytes.drop len, r.pos + len⟩
      return (id, (r.bytes.take len).toArray) :: rest

def moduleSections : Option (List (Nat × Array Nat)) := do
  if slice artifact 0 8 != #[0, 97, 115, 109, 1, 0, 0, 0] then none
  else sections 30 { bytes := artifact.toList.drop 8, pos := 8 }

def getSection (id : Nat) : Option (Array Nat) := do
  let ss ← moduleSections
  (ss.find? (fun s => s.1 == id)).map Prod.snd

def bodies : Nat → Reader → Option (List (Array Nat) × Reader)
  | 0, r => some ([], r)
  | n+1, r => do
    let (len, r) ← uleb r
    if len > r.bytes.length then none else do
      let (rest, r') ← bodies n ⟨r.bytes.drop len, r.pos + len⟩
      return ((r.bytes.take len).toArray :: rest, r')

def functionBodies : Option (List (Array Nat)) := do
  let bs ← getSection 10
  let (n, r) ← uleb { bytes := bs.toList }
  let (fs, r) ← bodies n r
  if r.bytes.isEmpty then some fs else none

def locals : Nat → Reader → Option (Nat × Reader)
  | 0, r => some (0, r)
  | n+1, r => do
    let (count, r) ← uleb r
    let (ty, r) ← byte r
    if ty != 127 && ty != 126 then none else do
      let (count', r) ← locals n r
      return (count + count', r)

structure Instr where
  op : Nat
  arg : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- A balanced instruction table keeps kernel reduction logarithmic per fetch.
The table is checked against the extracted flat instruction list. -/
inductive CodeTree where
  | empty
  | leaf (i : Instr)
  | node (leftSize : Nat) (left right : CodeTree)
  deriving Repr

def CodeTree.toList : CodeTree → List Instr
  | .empty => []
  | .leaf i => [i]
  | .node _ l r => l.toList ++ r.toList

def CodeTree.get? : CodeTree → Nat → Option Instr
  | .empty, _ => none
  | .leaf i, 0 => some i
  | .leaf _, _+1 => none
  | .node n l r, pc => if pc < n then l.get? pc else r.get? (pc-n)

def CodeTree.wellFormed : CodeTree → Bool
  | .empty | .leaf _ => true
  | .node n l r => n == l.toList.length && l.wellFormed && r.wellFormed

theorem CodeTree.get?_eq (t : CodeTree) (h : t.wellFormed = true) (pc : Nat) :
    t.get? pc = t.toList[pc]? := by
  induction t generalizing pc with
  | empty => simp [CodeTree.get?, CodeTree.toList]
  | leaf i => cases pc <;> simp [CodeTree.get?, CodeTree.toList]
  | node n l r ihl ihr =>
    simp only [CodeTree.wellFormed, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hn, hl⟩, hr⟩
    subst n
    simp [CodeTree.get?, CodeTree.toList, List.getElem?_append, ihl hl, ihr hr]

structure Code where
  tree : CodeTree
  size : Nat

def Code.get? (c : Code) (pc : Nat) : Option Instr :=
  if pc < c.size then c.tree.get? pc else none

def instruction (r : Reader) : Option (Instr × Reader) := do
  let (op, r) ← byte r
  if op == 2 || op == 3 then
    let (ty, r) ← byte r
    if ty == 64 then return (⟨op, 0⟩, r) else none
  else if [12, 13, 16, 32, 33, 34].contains op then
    let (arg, r) ← uleb r
    return (⟨op, arg⟩, r)
  else if [40, 41, 45, 47, 54, 55, 58, 59].contains op then
    let (_, r) ← uleb r -- alignment hint, not semantic
    let (offset, r) ← uleb r
    return (⟨op, offset⟩, r)
  else if op == 65 || op == 66 then
    let (arg, r) ← sleb (if op == 65 then 32 else 64) r
    return (⟨op, arg⟩, r)
  else if op == 252 then
    let (sub, r) ← uleb r
    let (mem, r) ← byte r
    if mem != 0 then none
    else if sub == 10 then
      let (mem2, r) ← byte r
      if mem2 == 0 then return (⟨256 + sub, 0⟩, r) else none
    else if sub == 11 then return (⟨256 + sub, 0⟩, r)
    else none
  else if [0, 11, 15, 27, 69, 70, 71, 73, 75, 77, 79,
           106, 107, 113, 114, 116, 118].contains op then
    return (⟨op, 0⟩, r)
  else none

def instructions : Nat → Reader → Option (List Instr)
  | 0, _ => none
  | n+1, r => do
    if r.bytes.isEmpty then return []
    let (i, r) ← instruction r
    let rest ← instructions n r
    return i :: rest

def extractedProgram : Option (Nat × Array Instr) := do
  let fs ← functionBodies
  let bs ← fs[7]?
  let (n, r) ← uleb { bytes := bs.toList }
  let (nlocals, r) ← locals n r
  let code ← instructions bs.size r
  return (nlocals, code.toArray)

-- A transparent, sparse byte memory. Unlisted addresses contain zero.
abbrev Memory := List (Nat × Nat)

def memByte (m : Memory) (addr : Nat) : Nat :=
  ((m.find? (fun p => p.1 == addr)).map Prod.snd).getD 0

def putBytes (m : Memory) (addr : Nat) (bs : List Nat) : Memory :=
  bs.zipIdx.foldl (fun m (b, i) => (addr+i, b % 256) :: m) m

def getBytes (m : Memory) (addr count : Nat) : List Nat :=
  (List.range count).map (fun i => memByte m (addr+i))

structure Access where
  write : Bool
  addr : Nat
  count : Nat
  deriving Repr, DecidableEq

structure Label where
  loop : Bool
  start : Nat
  finish : Nat
  height : Nat
  deriving Repr

structure State where
  pc : Nat := 0
  stack : List Nat := [] -- top first
  vars : Array Nat
  labels : List Label := []
  mem : Memory
  trace : List Access := [] -- reverse chronological
  deriving Repr

def modulus : Nat := 4294967296
def w32 (n : Nat) : Nat := n % modulus

def blockEnds : List Instr → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], _, _, ends => ends
  | i :: rest, pc, stack, ends =>
    if i.op == 2 || i.op == 3 then blockEnds rest (pc+1) (pc :: stack) ends
    else if i.op == 11 then
      match stack with
      | start :: stack => blockEnds rest (pc+1) stack ((start, pc) :: ends)
      | [] => blockEnds rest (pc+1) [] ends
    else blockEnds rest (pc+1) stack ends

/-- Cache structured label destinations. The extraction theorem checks this
preprocessing together with byte decoding; it is not assumed as a certificate. -/
def annotate (code : Array Instr) : Array Instr :=
  let ends := blockEnds code.toList 0 [] []
  (code.toList.zipIdx.map (fun (i, pc) =>
    if i.op == 2 || i.op == 3 then
      { i with arg := ((ends.find? (fun p => p.1 == pc)).map Prod.snd).getD code.size }
    else i)).toArray

def branch (depth : Nat) (s : State) : Option State := do
  let l ← s.labels[depth]?
  if s.stack.length < l.height then none else
    some { s with
      pc := if l.loop then l.start else l.finish+1
      stack := s.stack.drop (s.stack.length - l.height)
      labels := s.labels.drop (depth + if l.loop then 0 else 1) }

def littleValue (bs : List Nat) : Nat :=
  bs.foldr (fun b acc => b + 256*acc) 0

def valueBytes (n width : Nat) : List Nat :=
  (List.range width).map (fun i => (n / 256^i) % 256)

def loadWidth (op : Nat) : Nat :=
  if op == 40 then 4 else if op == 41 then 8 else if op == 45 then 1 else 2

def storeWidth (op : Nat) : Nat :=
  if op == 54 then 4 else if op == 55 then 8 else if op == 58 then 1 else 2

def binary (op x y : Nat) : Option Nat :=
  if op == 70 then some (if x == y then 1 else 0)
  else if op == 71 then some (if x != y then 1 else 0)
  else if op == 73 then some (if x < y then 1 else 0)
  else if op == 75 then some (if x > y then 1 else 0)
  else if op == 77 then some (if x ≤ y then 1 else 0)
  else if op == 79 then some (if x ≥ y then 1 else 0)
  else if op == 106 then some (w32 (x+y))
  else if op == 107 then some (w32 (x+modulus-y))
  else if op == 113 then some (Nat.land x y)
  else if op == 114 then some (Nat.lor x y)
  else if op == 116 then some (w32 (x * 2^(y%32)))
  else if op == 118 then some (x / 2^(y%32))
  else none

-- `none` means unsupported, trap, or malformed state. Calls are unsupported.
-- The outer `Except.ok` represents an actual i32 return, never an error sentinel
-- from the interpreter. `Except.error` continues execution.
def step (code : Code) (s : State) : Option (Except State (Nat × State)) := do
  let i ← code.get? s.pc
  let t := { s with pc := s.pc + 1 }
  if i.op == 2 || i.op == 3 then
    let last := i.arg
    if last ≥ code.size || ((code.get? last).getD default).op != 11 then none else
    return .error { t with labels :=
      ⟨i.op == 3, s.pc+1, last, s.stack.length⟩ :: s.labels }
  else if i.op == 11 then
    match s.labels with
    | [] =>
      match s.stack with
      | [v] => return .ok (v, t)
      | _ => none
    | l :: ls =>
      if s.pc != l.finish || s.stack.length != l.height then none
      else return .error { t with labels := ls }
  else if i.op == 12 then return .error (← branch i.arg s)
  else if i.op == 13 then
    match s.stack with
    | cond :: st =>
      if cond == 0 then return .error { t with stack := st }
      else return .error (← branch i.arg { s with stack := st })
    | _ => none
  else if i.op == 15 then
    match s.stack with
    | v :: _ => return .ok (v, t)
    | _ => none
  else if i.op == 32 then
    let v ← s.vars[i.arg]?
    return .error { t with stack := v :: s.stack }
  else if i.op == 33 || i.op == 34 then
    match s.stack with
    | v :: st =>
      if i.arg ≥ s.vars.size then none else
        let vs := s.vars.set! i.arg v
        return .error { t with
          vars := vs
          stack := if i.op == 34 then s.stack else st }
    | _ => none
  else if i.op == 65 || i.op == 66 then
    return .error { t with stack := i.arg :: s.stack }
  else if i.op == 27 then
    match s.stack with
    | cond :: y :: x :: st =>
      return .error { t with stack := (if cond != 0 then x else y) :: st }
    | _ => none
  else if i.op == 69 then
    match s.stack with
    | x :: st => return .error { t with stack := (if x == 0 then 1 else 0) :: st }
    | _ => none
  else if [40, 41, 45, 47].contains i.op then
    match s.stack with
    | a :: st =>
      let addr := a + i.arg
      let count := loadWidth i.op
      if addr + count > 2097152 then none else
        return .error { t with
          stack := littleValue (getBytes s.mem addr count) :: st
          trace := ⟨false, addr, count⟩ :: s.trace }
    | _ => none
  else if [54, 55, 58, 59].contains i.op then
    match s.stack with
    | v :: a :: st =>
      let addr := a + i.arg
      let count := storeWidth i.op
      if addr + count > 2097152 then none else
        return .error { t with
          stack := st
          mem := putBytes s.mem addr (valueBytes v count)
          trace := ⟨true, addr, count⟩ :: s.trace }
    | _ => none
  else if i.op == 266 || i.op == 267 then
    match s.stack with
    | count :: source :: dest :: st =>
      if dest + count > 2097152 || (i.op == 266 && source + count > 2097152) then none
      else
        let bs := if i.op == 266 then getBytes s.mem source count
          else List.replicate count (source % 256)
        let trace := ⟨true, dest, count⟩ :: s.trace
        return .error { t with
          stack := st
          mem := putBytes s.mem dest bs
          trace := if i.op == 266 then ⟨false, source, count⟩ :: trace else trace }
    | _ => none
  else
    match s.stack with
    | y :: x :: st =>
      let v ← binary i.op x y
      return .error { t with stack := v :: st }
    | _ => none

def execute : Nat → Code → State → Option (Nat × State)
  | 0, _, _ => none
  | fuel+1, code, s => do
    match ← step code s with
    | .ok result => return result
    | .error s => execute fuel code s

end LZ4Verification
