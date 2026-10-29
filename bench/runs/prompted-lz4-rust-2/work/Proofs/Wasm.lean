import Init

/- A fuelled interpreter for the integer, void-block subset used by the reachable
   functions of this artifact. Values are unsigned naturals; arithmetic wraps. -/
namespace Wasm
inductive Bin where
  | add | sub | mul | divU | band | bor | bxor | shl | shr | eq | ne | lt | le | gt | ge
  deriving BEq
inductive Instr where
  | const (value : Nat) | bin (op : Bin) (bits : Nat)
  | eqz | ctz | wrap | extend
  | getLocal (i : Nat) | setLocal (i : Nat) | teeLocal (i : Nat)
  | getGlobal (i : Nat) | setGlobal (i : Nat)
  | block (after : Nat) | loop (after : Nat) | endBlock
  | br (depth : Nat) | brIf (depth : Nat) | call (index : Nat)
  | load (bytes offset : Nat) | store (bytes offset : Nat)
  | copy | fill | select | ret | trap
structure Func where
  params : Nat
  locals : Nat
  returns : Bool
  code : Nat → Option Instr
abbrev Memory := Nat → Nat
structure Access where
  write : Bool
  addr : Nat
  size : Nat
  deriving BEq, Repr
structure Label where
  again : Option Nat
  after : Nat
  stack : List Nat
structure Caller where
  func : Nat
  pc : Nat
  locals : List Nat
  labels : List Label
  stack : List Nat
  returns : Bool
inductive Status where
  | running | done (value : Nat) | trap | exhausted
  deriving BEq, Repr
structure State where
  func : Nat := 7
  pc : Nat := 0
  locals : List Nat := []
  globals : List Nat := [65536]
  stack : List Nat := []
  labels : List Label := []
  callers : List Caller := []
  returns : Bool := true
  mem : Memory
  accesses : List Access := []
  status : Status := .running

def modulus (bits : Nat) := 2 ^ bits
def evalBin (op : Bin) (bits a b : Nat) : Nat :=
  let m := modulus bits
  match op with
  | .add => (a + b) % m
  | .sub => (a + m - b) % m
  | .mul => (a * b) % m
  | .divU => a / b
  | .band => Nat.land a b | .bor => Nat.lor a b | .bxor => Nat.xor a b
  | .shl => (a * 2 ^ (b % bits)) % m | .shr => a / 2 ^ (b % bits)
  | .eq => if a = b then 1 else 0 | .ne => if a ≠ b then 1 else 0
  | .lt => if a < b then 1 else 0 | .le => if a ≤ b then 1 else 0
  | .gt => if a > b then 1 else 0 | .ge => if a ≥ b then 1 else 0

def trailing : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, v => if v % 2 = 1 then 0 else 1 + trailing n (v / 2)
def readLE (m : Memory) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => m a + 256 * readLE m (a+1) n
def writeLE (m : Memory) (a n v : Nat) : Memory :=
  fun x => if a ≤ x ∧ x < a+n then v / 256^(x-a) % 256 else m x

def finish (s : State) : State :=
  match s.callers with
  | [] => { s with status := .done (s.stack.headD 0) }
  | c :: cs => { s with func := c.func, pc := c.pc, locals := c.locals, labels := c.labels, stack := (if s.returns then s.stack.headD 0 :: c.stack else c.stack), returns := c.returns, callers := cs }
def branch (s : State) (depth : Nat) : State :=
  match s.labels[depth]? with
  | none => { s with status := .trap }
  | some l => match l.again with
    | none => { s with pc := l.after, stack := l.stack, labels := s.labels.drop (depth+1) }
    | some body => { s with pc := body, stack := l.stack, labels := s.labels.drop depth }

def step (program : Nat → Option Func) (s : State) : State := Id.run do
  let bad := { s with status := .trap }
  match (program s.func).bind (fun f => f.code s.pc) with
  | none => return bad
  | some ins =>
    let t := { s with pc := s.pc+1 }
    match ins, s.stack with
    | .const v, st => return { t with stack := v :: st }
    | .bin op bits, b :: a :: st =>
      if op == .divU && b == 0 then return bad
      return { t with stack := evalBin op bits a b :: st }
    | .eqz, v :: st => return { t with stack := (if v = 0 then 1 else 0) :: st }
    | .ctz, v :: st => return { t with stack := trailing 32 v :: st }
    | .wrap, v :: st => return { t with stack := v % modulus 32 :: st }
    | .extend, _ => return t
    | .getLocal i, st =>
      match s.locals[i]? with
      | none => return bad
      | some v => return { t with stack := v :: st }
    | .setLocal i, v :: st =>
      if i ≥ s.locals.length then return bad
      return { t with locals := s.locals.set i v, stack := st }
    | .teeLocal i, v :: _ =>
      if i ≥ s.locals.length then return bad
      return { t with locals := s.locals.set i v }
    | .getGlobal i, st =>
      match s.globals[i]? with
      | none => return bad
      | some v => return { t with stack := v :: st }
    | .setGlobal i, v :: st =>
      if i ≥ s.globals.length then return bad
      return { t with globals := s.globals.set i v, stack := st }
    | .block after, _ =>
      return { t with labels := ⟨none, after, s.stack⟩ :: s.labels }
    | .loop after, _ =>
      return { t with labels := ⟨some (s.pc+1), after, s.stack⟩ :: s.labels }
    | .endBlock, _ =>
      match s.labels with
      | [] => return bad
      | _ :: ls => return { t with labels := ls }
    | .br d, _ => return branch t d
    | .brIf d, v :: st =>
      let t := { t with stack := st }
      return if v = 0 then t else branch t d
    | .call i, st =>
      match program i with
      | none => return bad
      | some f =>
        if st.length < f.params then return bad
        let c := ⟨s.func, s.pc+1, s.locals, s.labels, st.drop f.params, s.returns⟩
        return { t with func := i, pc := 0, locals := (st.take f.params).reverse ++ List.replicate f.locals 0, stack := [], labels := [], callers := c :: s.callers, returns := f.returns }
    | .load n off, a :: st =>
      let addr := a + off
      if addr+n > 2097152 then return bad
      return { t with stack := readLE s.mem addr n :: st, accesses := ⟨false, addr, n⟩ :: s.accesses }
    | .store n off, v :: a :: st =>
      let addr := a + off
      if addr+n > 2097152 then return bad
      return { t with stack := st, mem := writeLE s.mem addr n v, accesses := ⟨true, addr, n⟩ :: s.accesses }
    | .copy, n :: src :: dst :: st =>
      if src+n > 2097152 ∨ dst+n > 2097152 then return bad
      return { t with stack := st, mem := (fun x => if dst ≤ x ∧ x < dst+n then s.mem (src+x-dst) else s.mem x), accesses := ⟨true, dst, n⟩ :: ⟨false, src, n⟩ :: s.accesses }
    | .fill, n :: v :: dst :: st =>
      if dst+n > 2097152 then return bad
      return { t with stack := st, mem := (fun x => if dst ≤ x ∧ x < dst+n then v % 256 else s.mem x), accesses := ⟨true, dst, n⟩ :: s.accesses }
    | .select, c :: b :: a :: st => return { t with stack := (if c = 0 then b else a) :: st }
    | .ret, _ => return finish t
    | _, _ => return bad

def run (program : Nat → Option Func) : Nat → State → State
  | 0, s => if s.status == .running then { s with status := .exhausted } else s
  | fuel+1, s => if s.status == .running then run program fuel (step program s) else s

def start (f : Func) (src dst n cap : Nat) (mem : Memory) : State :=
  { func := 7, pc := 0, locals := [src, dst, n, cap] ++ List.replicate f.locals 0, mem := mem, returns := f.returns }
end Wasm
