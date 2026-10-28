/- A deliberately restricted Wasm32 reader and interpreter. Unsupported instructions fail. -/
namespace Wasm
abbrev Bytes := List Nat
abbrev Mem := Nat → Nat
def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def truth (p : Prop) [Decidable p] : Nat := if p then 1 else 0

-- LEB128, bounded to five bytes (the only integer width used by the decoder).
def leb (signed : Bool) : Nat → Bytes → Nat → Nat → Option (Nat × Bytes)
  | 0, _, _, _ => none
  | fuel+1, b::bs, shift, acc =>
    let n := acc + (b % 128) * 2^shift
    if b < 128 then
      some ((if signed && b ≥ 64 then n + modulus - 2^(shift+7) else n), bs)
    else leb signed fuel bs (shift+7) n
  | _, [], _, _ => none
def uleb (bs : Bytes) := leb false 5 bs 0 0
def sleb (bs : Bytes) := leb true 5 bs 0 0

def chunks : Nat → Bytes → Option (List (Nat × Bytes))
  | 0, [] => some []
  | 0, _ => none
  | _+1, [] => some []
  | fuel+1, tag::bs => do
    let (size, bs) ← uleb bs
    if size > bs.length then none else do
      let rest ← chunks fuel (bs.drop size)
      pure ((tag, bs.take size)::rest)
def getSection (ss : List (Nat × Bytes)) (id : Nat) : Bytes :=
  ((ss.find? fun s => s.1 == id).map Prod.snd).getD []
def sections (bs : Bytes) : Option (List (Nat × Bytes)) :=
  if bs.take 8 == [0,97,115,109,1,0,0,0] then chunks bs.length (bs.drop 8) else none

def sized : Nat → Bytes → Option (List Bytes × Bytes)
  | 0, bs => some ([], bs)
  | n+1, bs => do
    let (size, bs) ← uleb bs
    if size > bs.length then none else do
      let (rest, tail) ← sized n (bs.drop size)
      pure (bs.take size::rest, tail)
def bodies (ss : List (Nat × Bytes)) : Option (List Bytes) := do
  let (n, bs) ← uleb (getSection ss 10)
  let (out, tail) ← sized n bs
  if tail.isEmpty then some out else none

structure Instr where
  op : Nat
  a : Nat := 0
  b : Nat := 0
  deriving Repr, DecidableEq

def instructions : Nat → Bytes → Option (List Instr)
  | 0, [] => some []
  | 0, _ => none
  | _+1, [] => some []
  | fuel+1, op::bs => do
    let (i, tail) ←
      if op == 2 || op == 3 then
        match bs with
        | 64::rest => some (⟨op,0,0⟩,rest) -- void block / loop
        | _ => none
      else if [12,13,16,32,33,34].contains op then do
        let (a, rest) ← uleb bs
        pure (⟨op,a,0⟩,rest)
      else if [40,45,47,54,58].contains op then do
        let (align, rest) ← uleb bs
        let (offset, rest) ← uleb rest
        pure (⟨op,align,offset⟩,rest)
      else if op == 65 then do
        let (a, rest) ← sleb bs
        pure (⟨op,word a,0⟩,rest)
      else if [11,15,26,27,69,70,71,72,73,75,77,79,106,107,113,115,116,118].contains op then
        some (⟨op,0,0⟩,bs)
      else none
    let rest ← instructions fuel tail
    pure (i::rest)

structure Func where
  locals : Nat
  code : List Instr
  deriving Repr, DecidableEq

def function (bs : Bytes) : Option Func := do
  let (groups, bs) ← uleb bs
  let (n, bs) ← if groups == 1 then uleb bs else none
  let bs ← match bs with | 127::rest => some rest | _ => none
  let code ← instructions bs.length bs
  pure ⟨n, code⟩

-- Only functions 2, 3 and 4 are reachable from export LZ4_decompress_safe.
def program (artifact : Bytes) : Option (List Func) := do
  let ss ← sections artifact
  let fs ← bodies ss
  let d ← function (← fs[2]?)
  let c ← function (← fs[3]?)
  let m ← function (← fs[4]?)
  pure [d,c,m]

structure Label where
  start : Nat
  finish : Nat
  height : Nat
  loop : Bool
  deriving Repr
structure Activation where
  fn : Nat
  pc : Nat
  locals : List Nat
  stack : List Nat
  labels : List Label
structure Access where
  write : Bool
  address : Nat
  width : Nat
  deriving Repr, DecidableEq
structure State where
  fn : Nat := 0
  pc : Nat := 0
  locals : List Nat := []
  stack : List Nat := []
  labels : List Label := []
  calls : List Activation := []
  mem : Mem
  trace : List Access := []

-- Find the matching 'end', counting nested blocks and loops.
def closing : Nat → List Instr → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | _+1, [], _, _ => none
  | fuel+1, i::is, pc, depth =>
    if i.op == 11 then
      if depth == 0 then some pc else closing fuel is (pc+1) (depth-1)
    else closing fuel is (pc+1) (if i.op == 2 || i.op == 3 then depth+1 else depth)

def load (m : Mem) (addr : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m addr % 256 + 256 * load m (addr+1) n
def store (m : Mem) (addr value : Nat) : Nat → Mem
  | 0 => m
  | n+1 => store (fun p => if p == addr then value % 256 else m p)
      (addr+1) (value/256) n

def jump (s : State) (depth : Nat) : Option State := do
  let l ← s.labels[depth]?
  pure { s with pc := if l.loop then l.start else l.finish+1
                stack := s.stack.drop (s.stack.length-l.height)
                labels := s.labels.drop (if l.loop then depth else depth+1) }

def binary (op x y : Nat) : Option Nat :=
  match op with
  | 70 => some (truth (x=y)) | 71 => some (truth (x≠y))
  | 72 => some (truth ((x + 2147483648) % modulus < (y + 2147483648) % modulus))
  | 73 => some (truth (x<y)) | 75 => some (truth (x>y))
  | 77 => some (truth (x≤y)) | 79 => some (truth (x≥y))
  | 106 => some (word (x+y)) | 107 => some (word (x+modulus-y))
  | 113 => some (Nat.land x y) | 115 => some (Nat.xor x y)
  | 116 => some (word (x*2^(y%32))) | 118 => some (x/2^(y%32))
  | _ => none

inductive Step where
  | next : State → Step
  | done : Nat → State → Step

def ret (s : State) : Option Step := do
  let v ← s.stack.head?
  match s.calls with
  | [] => pure (.done v s)
  | a::rest => pure (.next { s with fn := a.fn, pc := a.pc, locals := a.locals, stack := v::a.stack, labels := a.labels, calls := rest })

def step (fs : List Func) (s : State) : Option Step := do
  let f ← fs[s.fn]?
  let i ← f.code[s.pc]?
  let t := { s with pc := s.pc+1 }
  let next := fun (s : State) => some (Step.next s)
  match i.op with
  | 2 | 3 => do
    let stop ← closing f.code.length (f.code.drop (s.pc+1)) (s.pc+1) 0
    next { t with labels := ⟨s.pc+1, stop, s.stack.length, i.op == 3⟩::s.labels }
  | 11 => match s.labels with
    | [] => ret s
    | _::ls => next { t with labels := ls }
  | 12 => return .next (← jump s i.a)
  | 13 => do
    let x::xs := s.stack | none
    if x == 0 then next {t with stack := xs} else return .next (← jump {s with stack := xs} i.a)
  | 15 => ret s
  | 16 => do
    let fn ← if i.a == 3 then some 1 else if i.a == 4 then some 2 else none
    let target ← fs[fn]?
    let z::y::x::xs := s.stack | none
    next { t with fn := fn, pc := 0, locals := [x,y,z] ++ List.replicate target.locals 0, stack := [], labels := [], calls := ⟨s.fn,s.pc+1,s.locals,xs,s.labels⟩::s.calls }
  | 26 => do
    let _::xs := s.stack | none
    next {t with stack := xs}
  | 27 => do
    let c::y::x::xs := s.stack | none
    next {t with stack := (if c == 0 then y else x)::xs}
  | 32 => do
    let v ← s.locals[i.a]?
    next {t with stack := v::s.stack}
  | 33 | 34 => do
    let v::xs := s.stack | none
    if i.a ≥ s.locals.length then none else
      next {t with locals := s.locals.set i.a v, stack := if i.op == 34 then s.stack else xs}
  | 40 | 45 | 47 => do
    let a::xs := s.stack | none
    let w := if i.op == 40 then 4 else if i.op == 47 then 2 else 1
    let addr := a+i.b
    if addr+w > 2097152 then none else
      next {t with stack := load s.mem addr w::xs, trace := ⟨false,addr,w⟩::s.trace}
  | 54 | 58 => do
    let v::a::xs := s.stack | none
    let w := if i.op == 54 then 4 else 1
    let addr := a+i.b
    if addr+w > 2097152 then none else
      next {t with stack := xs, mem := store s.mem addr v w, trace := ⟨true,addr,w⟩::s.trace}
  | 65 => next {t with stack := i.a::s.stack}
  | 69 => do
    let v::xs := s.stack | none
    next {t with stack := truth (v=0)::xs}
  | _ => do
    let y::x::xs := s.stack | none
    let v ← binary i.op x y
    next {t with stack := v::xs}

def run (fs : List Func) : Nat → State → Option (Nat × State)
  | 0, _ => none
  | fuel+1, s => do
    match ← step fs s with
    | .done v t => pure (v,t)
    | .next t => run fs fuel t

def start (fs : List Func) (mem : Mem) (src dst size cap : Nat) : State :=
  { locals := [src,dst,size,cap] ++ List.replicate ((fs[0]?).map Func.locals |>.getD 0) 0, mem := mem }
end Wasm
