import Proofs.Code
set_option autoImplicit false
namespace Wasm
-- All addresses and operand values are unsigned i32; signedness is per operation.
def word (n : Nat) : Nat := n % 2^32
def signed (n : Nat) : Int := if n < 2^31 then n else (n : Int) - 2^32
abbrev Memory := Nat → Nat
structure Access where
  write : Bool
  addr : Nat
  width : Nat
  deriving Repr, BEq, DecidableEq
structure Label where
  afterCode : List Instr
  loopCode : Option (List Instr)
  stack : List Nat
structure Caller where
  code : List Instr
  locals : List Nat
  stack : List Nat
  labels : List Label
structure State where
  code : List Instr
  locals : List Nat
  stack : List Nat := []
  labels : List Label := []
  callers : List Caller := []
  mem : Memory
  accesses : List Access := []
inductive Result where
  | running : State → Result
  | returned : Nat → State → Result
  | trap : Result
-- Block types in these three functions are empty. Labels save their entry stack.
def afterEnd : Nat → List Instr → Option (List Instr)
  | _, [] => none
  | depth, i :: is =>
    if i.op == 2 || i.op == 3 then afterEnd (depth+1) is
    else if i.op == 11 then
      if depth == 0 then some is else afterEnd (depth-1) is
    else afterEnd depth is
def returnFrom (s : State) : Result :=
  match s.stack with
  | [] => .trap
  | v :: _ => match s.callers with
    | [] => .returned v s
    | c :: cs => .running { s with code := c.code, locals := c.locals, stack := v :: c.stack, labels := c.labels, callers := cs }
def branch (n : Nat) (s : State) : Result :=
  match s.labels[n]? with
  | none => .trap
  | some l => .running { s with
      code := l.loopCode.getD l.afterCode
      stack := l.stack
      labels := s.labels.drop (if l.loopCode.isSome then n else n+1) }
def loadBytes (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m a % 256 + 256 * loadBytes m (a+1) n
def storeBytes (m : Memory) (a v : Nat) : Nat → Memory
  | 0 => m
  | n+1 => match v % 256 with
    | 0 => storeBytes (fun p => if p == a then 0 else m p) (a+1) (v/256) n
    | b+1 => storeBytes (fun p => if p == a then b+1 else m p) (a+1) (v/256) n
def binary (op a b : Nat) : Option Nat :=
  if op == 70 then some (if a == b then 1 else 0)
  else if op == 71 then some (if a != b then 1 else 0)
  else if op == 72 then some (if signed a < signed b then 1 else 0)
  else if op == 73 then some (if a < b then 1 else 0)
  else if op == 75 then some (if a > b then 1 else 0)
  else if op == 77 then some (if a ≤ b then 1 else 0)
  else if op == 79 then some (if a ≥ b then 1 else 0)
  else if op == 106 then some (word (a+b))
  else if op == 107 then some (word (a+2^32-b))
  else if op == 113 then some (Nat.land a b)
  else if op == 115 then some (Nat.xor a b)
  else if op == 116 then some (word (a * 2^(b%32)))
  else if op == 118 then some (a / 2^(b%32))
  else none
def step (s : State) : Result := Id.run do
  let i :: rest := s.code | return .trap
  let t := { s with code := rest }
  if i.op == 2 || i.op == 3 then
    let some after := afterEnd 0 rest | return .trap
    return .running { t with labels := ⟨after, if i.op == 3 then some rest else none,
      s.stack⟩ :: s.labels }
  if i.op == 11 then
    match s.labels with
    | [] => return returnFrom t
    | l :: ls => return .running { t with code := l.afterCode, labels := ls }
  if i.op == 15 then return returnFrom t
  if i.op == 12 then return branch i.a t
  if i.op == 13 then
    let c :: vs := s.stack | return .trap
    let t := { t with stack := vs }
    return if c == 0 then .running t else branch i.a t
  if i.op == 16 then
    -- Only these reachable functions have the signatures used by the decoder.
    if !(i.a == 3 || i.a == 4) then return .trap
    let some f := function i.a | return .trap
    let n :: src :: dst :: vs := s.stack | return .trap
    return .running { t with code := f.code, locals := [dst,src,n] ++ List.replicate f.locals 0, stack := [], labels := [], callers := ⟨rest,s.locals,vs,s.labels⟩ :: s.callers }
  if i.op == 65 then return .running { t with stack := i.a :: s.stack }
  if i.op == 32 then
    let some v := s.locals[i.a]? | return .trap
    return .running { t with stack := v :: s.stack }
  if i.op == 33 || i.op == 34 then
    let v :: vs := s.stack | return .trap
    if i.a ≥ s.locals.length then return .trap
    return .running { t with locals := s.locals.set i.a v, stack := if i.op == 34 then s.stack else vs }
  if i.op == 26 then
    let _ :: vs := s.stack | return .trap
    return .running { t with stack := vs }
  if i.op == 27 then
    let c :: b :: a :: vs := s.stack | return .trap
    return .running { t with stack := (if c == 0 then b else a) :: vs }
  if i.op == 69 then
    let a :: vs := s.stack | return .trap
    return .running { t with stack := (if a == 0 then 1 else 0) :: vs }
  if [40,45,47].contains i.op then
    let a :: vs := s.stack | return .trap
    let addr := a + i.a
    let width := if i.op == 40 then 4 else if i.op == 47 then 2 else 1
    if addr + width > 2097152 then return .trap
    return .running { t with stack := loadBytes s.mem addr width :: vs, accesses := ⟨false,addr,width⟩ :: s.accesses }
  if i.op == 54 || i.op == 58 then
    let v :: a :: vs := s.stack | return .trap
    let addr := a + i.a
    let width := if i.op == 54 then 4 else 1
    if addr + width > 2097152 then return .trap
    return .running { t with stack := vs, mem := storeBytes s.mem addr v width, accesses := ⟨true,addr,width⟩ :: s.accesses }
  let b :: a :: vs := s.stack | return .trap
  let some v := binary i.op a b | return .trap
  return .running { t with stack := v :: vs }
def run : Nat → State → Result
  | 0, s => .running s
  | fuel+1, s => match step s with
    | .running t => run fuel t
    | r => r
def start (src dst size cap : Nat) (m : Memory) : Option State := do
  let f ← function 2
  return { code := f.code, locals := [src,dst,size,cap] ++ List.replicate f.locals 0, mem := m }
def execute (fuel src dst size cap : Nat) (m : Memory) : Result :=
  match start src dst size cap m with
  | none => .trap
  | some s => run fuel s
end Wasm
