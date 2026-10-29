import Init

/-- The subset of WebAssembly executed by the exported decoder. Unsupported paths fail closed. -/
structure Insn where
  op : Nat
  arg : Nat := 0
  off : Nat := 0
  deriving DecidableEq, Repr, Inhabited

def uleb : Nat → List Nat → Option (Nat × Nat × Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, 7, b, bs) else do
      let (n, bits, last, rest) ← uleb fuel bs
      pure (b % 128 + 128 * n, bits + 7, last, rest)

def immediate (signed : Nat) (bs : List Nat) : Option (Nat × List Nat) := do
  let (n, bits, last, rest) ← uleb 10 bs
  let value := if signed == 0 then n else
    if last % 128 < 64 then n % 2^signed
    else ((n : Int) - (2^bits : Nat)).emod (2^signed) |>.toNat
  pure (value, rest)

def decode : Nat → List Nat → Option (List Insn)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, op :: bs => do
    let (ins, rest) ←
      if op == 2 || op == 3 then
        match bs with
        | 64 :: rest => some (Insn.mk op 64 0, rest)
        | _ => none
      else if [12,13,16,32,33,34].contains op then do
        let (a, rest) ← immediate 0 bs
        pure (Insn.mk op a 0, rest)
      else if [40,41,45,47,54,55,58,59].contains op then do
        let (a, rest) ← immediate 0 bs
        let (o, rest) ← immediate 0 rest
        pure (Insn.mk op a o, rest)
      else if op == 65 || op == 66 then do
        let (a, rest) ← immediate (if op == 65 then 32 else 64) bs
        pure (Insn.mk op a 0, rest)
      else if op == 252 then do
        let (a, rest) ← immediate 0 bs
        match a, rest with
        | 10, 0 :: 0 :: rest => pure (Insn.mk op a 0, rest)
        | 11, 0 :: rest => pure (Insn.mk op a 0, rest)
        | _, _ => none
      else if [0,11,15,27,69,70,71,73,75,77,79,106,107,113,114,118].contains op then
        pure (Insn.mk op 0 0, bs)
      else none
    let tail ← decode fuel rest
    pure (ins :: tail)

def checkNesting : List Insn → List Nat → Nat → List Nat → Bool
  | [], [], _, [] => true
  | ins :: code, target :: ends, pc, stack =>
    if ins.op == 2 || ins.op == 3 then
      checkNesting code ends (pc+1) (target :: stack)
    else if ins.op == 11 then
      match stack with
      | [] => code.isEmpty && ends.isEmpty
      | e :: stack => pc == e && checkNesting code ends (pc+1) stack
    else checkNesting code ends (pc+1) stack
  | _, _, _, _ => false

def checkEnds (code : Array Insn) (ends : Array Nat) : Bool :=
  checkNesting code.toList ends.toList 0 []

abbrev Memory := List (Nat × Nat)
def readByte (m : Memory) (a : Nat) : Nat :=
  match m.find? (fun kv => kv.1 == a) with
  | some kv => kv.2
  | none => 0

def readWord (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => readByte m a + 256 * readWord m (a+1) n

def writeWord (m : Memory) (a v : Nat) : Nat → Memory
  | 0 => m
  | n+1 => writeWord ((a, v%256)::m) (a+1) (v/256) n

def putBytes (m : Memory) (a : Nat) (bs : List Nat) : Memory :=
  (bs.zipIdx.map fun (b,i) => (a+i,b)) ++ m

structure Access where
  write : Bool
  addr : Nat
  size : Nat
  deriving DecidableEq, Repr, Inhabited

structure Label where
  loop : Bool
  start : Nat
  finish : Nat
  height : Nat
  deriving DecidableEq, Repr, Inhabited

structure State where
  pc : Nat := 0
  locals : List Nat
  stack : List Nat := []
  labels : List Label := []
  mem : Memory := []
  accesses : List Access := []
  result : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

def branch (s : State) (n : Nat) : Option State := do
  let l ← s.labels[n]?
  pure { s with pc := if l.loop then l.start else l.finish+1
                stack := s.stack.drop (s.stack.length-l.height)
                labels := s.labels.drop (if l.loop then n else n+1) }

def binop (op a b : Nat) : Option Nat :=
  let bit (p : Prop) [Decidable p] := if p then 1 else 0
  match op with
  | 70 => some (bit (a=b))
  | 71 => some (bit (a≠b))
  | 73 => some (bit (a<b))
  | 75 => some (bit (a>b))
  | 77 => some (bit (a≤b))
  | 79 => some (bit (a≥b))
  | 106 => some ((a+b) % 2^32)
  | 107 => some ((a+2^32-b) % 2^32)
  | 113 => some (Nat.land a b)
  | 114 => some (Nat.lor a b)
  | 118 => some (a / 2^(b%32))
  | _ => none

def step (code : Array Insn) (ends : Array Nat) (s : State) : Option State := do
  let i ← code[s.pc]?
  let t := { s with pc := s.pc+1 }
  match i.op, s.stack with
  | 2, _ | 3, _ =>
    let finish ← ends[s.pc]?
    pure { t with labels := ⟨i.op==3, s.pc+1, finish, s.stack.length⟩ :: s.labels }
  | 11, _ =>
    match s.labels with
    | [] => do let v ← s.stack.head?; pure { t with result := some v }
    | _ :: ls => pure { t with labels := ls }
  | 12, _ => branch s i.arg
  | 13, c :: st =>
    if c == 0 then pure { t with stack := st } else branch { s with stack := st } i.arg
  | 15, v :: _ => pure { t with result := some v }
  | 27, c :: b :: a :: st => pure { t with stack := (if c≠0 then a else b) :: st }
  | 32, st => do let v ← s.locals[i.arg]?; pure { t with stack := v :: st }
  | 33, v :: st => if i.arg < s.locals.length then
      pure { t with locals := s.locals.set i.arg v, stack := st } else none
  | 34, v :: _ => if i.arg < s.locals.length then
      pure { t with locals := s.locals.set i.arg v } else none
  | 65, st | 66, st => pure { t with stack := i.arg :: st }
  | 69, v :: st => pure { t with stack := (if v==0 then 1 else 0) :: st }
  | 40, a :: st | 41, a :: st | 45, a :: st | 47, a :: st =>
    let w := if i.op==41 then 8 else if i.op==40 then 4 else if i.op==47 then 2 else 1
    if a+i.off+w ≤ 2097152 then
      pure { t with stack := readWord s.mem (a+i.off) w :: st
                    accesses := ⟨false, a+i.off, w⟩ :: s.accesses } else none
  | 54, v :: a :: st | 55, v :: a :: st | 58, v :: a :: st | 59, v :: a :: st =>
    let w := if i.op==55 then 8 else if i.op==54 then 4 else if i.op==59 then 2 else 1
    if a+i.off+w ≤ 2097152 then
      pure { t with stack := st, mem := writeWord s.mem (a+i.off) v w
                    accesses := ⟨true, a+i.off, w⟩ :: s.accesses } else none
  | 252, n :: b :: a :: st =>
    if a+n ≤ 2097152 then
      if i.arg==10 then
        if b+n ≤ 2097152 then
          let bs := (List.range n).map (fun j => readByte s.mem (b+j))
          pure { t with stack := st, mem := putBytes s.mem a bs
                        accesses := ⟨true,a,n⟩ :: ⟨false,b,n⟩ :: s.accesses } else none
      else if i.arg==11 then
        pure { t with stack := st, mem := putBytes s.mem a (List.replicate n (b%256))
                      accesses := ⟨true,a,n⟩ :: s.accesses } else none
    else none
  | op, b :: a :: st => do
    let v ← binop op a b
    pure { t with stack := v :: st }
  | _, _ => none

def run (code : Array Insn) (ends : Array Nat) : Nat → State → Option State
  | 0, _ => none
  | fuel+1, s => if s.result.isSome then some s else do
    run code ends fuel (← step code ends s)

def initial (src dst n cap : Nat) (mem : Memory) : State :=
  { locals := [src,dst,n,cap] ++ List.replicate 24 0, mem := mem }

def observe (s : Option State) : Option (Nat × Memory × List Access) := do
  let s ← s
  let r ← s.result
  pure (r, s.mem, s.accesses)
