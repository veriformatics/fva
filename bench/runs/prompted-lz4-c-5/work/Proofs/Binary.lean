import Proofs.Bytes
set_option autoImplicit false
namespace Wasm
abbrev Bytes := List Nat
abbrev Reader (α : Type) := Nat → Option (α × Nat)
def byte : Reader Nat := fun pos => do
  let b ← Artifact.byteAt pos
  return (b, pos+1)
def ulebAux : Nat → Nat → Nat → Reader Nat
  | 0, _, _, _ => none
  | n+1, acc, shift, pos => do
    let (b, pos) ← byte pos
    let a := acc + (b % 128) * 2^shift
    if b < 128 then return (a, pos)
    else ulebAux n a (shift+7) pos
def uleb : Reader Nat := ulebAux 5 0 0
def slebAux : Nat → Nat → Nat → Reader Nat
  | 0, _, _, _ => none
  | n+1, acc, shift, pos => do
    let (b, pos) ← byte pos
    let a := acc + (b % 128) * 2^shift
    let bits := shift + 7
    if b < 128 then
      return ((if b ≥ 64 && bits < 32 then a + 2^32 - 2^bits else a) % 2^32, pos)
    else slebAux n a bits pos
def sleb : Reader Nat := slebAux 5 0 0
def vec {α : Type} (read : Reader α) : Nat → Reader (List α)
  | 0, pos => some ([], pos)
  | n+1, pos => do
    let (x, pos) ← read pos
    let (xs, pos) ← vec read n pos
    return (x :: xs, pos)
def spanBytes (pos len : Nat) : Option Bytes :=
  (List.range len).mapM fun k => Artifact.byteAt (pos+k)
def findSection : Nat → Nat → Reader (Nat × Nat)
  | 0, _, _ => none
  | n+1, id, pos => do
    let (tag, pos) ← byte pos
    let (len, pos) ← uleb pos
    if tag == id then return ((pos,len),pos+len)
    else findSection n id (pos+len)
def sectionSpan (id : Nat) : Option (Nat × Nat) := do
  let header ← spanBytes 0 8
  if header != [0,97,115,109,1,0,0,0] then none else
    let (span, _) ← findSection 32 id 8
    return span
def getSection (id : Nat) : Option Bytes := do
  let (pos,len) ← sectionSpan id
  spanBytes pos len
def findBody : Nat → Nat → Reader (Nat × Nat)
  | 0, _, _ => none
  | n+1, index, pos => do
    let (len, pos) ← uleb pos
    if index == 0 then return ((pos,len),pos+len)
    else findBody n (index-1) (pos+len)
def bodySpan (index : Nat) : Option (Nat × Nat) := do
  let (pos, _) ← sectionSpan 10
  let (n, pos) ← uleb pos
  let (span, _) ← findBody n index pos
  return span
structure Instr where
  op : Nat
  a : Nat := 0
  b : Nat := 0
  deriving Repr, BEq, DecidableEq
def instruction : Reader Instr := fun bs => do
  let (op, bs) ← byte bs
  if op == 2 || op == 3 then
    let (ty, bs) ← byte bs
    if ty == 64 then return (⟨op, 0, 0⟩, bs) else none
  else if [12,13,16,32,33,34].contains op then
    let (a, bs) ← uleb bs
    return (⟨op, a, 0⟩, bs)
  else if [40,45,47,54,58].contains op then
    let (align, bs) ← uleb bs
    let (offset, bs) ← uleb bs
    return (⟨op, offset, align⟩, bs)
  else if op == 65 then
    let (a, bs) ← sleb bs
    return (⟨op, a, 0⟩, bs)
  else if [11,15,26,27,69,70,71,72,73,75,77,79,106,107,113,115,116,118].contains op then
    return (⟨op, 0, 0⟩, bs)
  else none
def instructionsAux : Nat → Nat → Nat → List Instr → Option (List Instr × Nat)
  | 0, _, _, _ => none
  | n+1, stop, pos, acc => if pos == stop then some (acc.reverse, pos)
    else if pos > stop then none else do
      let (i, pos) ← instruction pos
      instructionsAux n stop pos (i :: acc)
def instructions (fuel stop : Nat) : Reader (List Instr) :=
  fun pos => instructionsAux fuel stop pos []
structure Func where
  locals : Nat
  code : List Instr
  deriving Repr, BEq, DecidableEq
def localGroup : Reader Nat := fun bs => do
  let (n, bs) ← uleb bs
  let (ty, bs) ← byte bs
  if ty == 127 then return (n, bs) else none
def parseFunction (index : Nat) : Option Func := do
  let (pos, len) ← bodySpan index
  let stop := pos+len
  let (n, pos) ← uleb pos
  let (groups, pos) ← vec localGroup n pos
  let (code, tail) ← instructions (len+1) stop pos
  if tail == stop then some ⟨groups.sum, code⟩ else none
end Wasm
