import Mathlib.Data.List.Basic

namespace Verification

-- Values are unsigned natural representatives of Wasm i32/i64 bitvectors.
inductive Op where
  | block (isLoop : Bool) (endPC : Nat) | end | br (depth : Nat) | brIf (depth : Nat)
  | const (v : Nat) | get (i : Nat) | set (i : Nat) | tee (i : Nat)
  | add | sub | and | shr | eq | ne | eqz | gt | ge | lt | le | select
  | load (width offset : Nat) | store (width offset : Nat) | copy | fill
  | ret | trap | call (index : Nat)
  deriving Repr, Inhabited

-- Balanced instruction table keeps kernel evaluation of instruction fetch logarithmic.
inductive Code where
  | leaf (op : Op)
  | node (leftSize : Nat) (left right : Code)
  deriving Inhabited

def fetch : Code → Nat → Option Op
  | .leaf op, 0 => some op
  | .leaf _, _+1 => none
  | .node n left right, i => if i < n then fetch left i else fetch right (i-n)

structure Label where
  target : Nat
  height : Nat
  isLoop : Bool
  deriving Repr, Inhabited

structure Access where
  write : Bool
  addr : Nat
  size : Nat
  deriving Repr, Inhabited

structure State where
  pc : Nat := 0
  stack : List Nat := []
  locals : Array Nat
  labels : List Label := []
  -- Latest store first; unwritten memory is specified by the initial-memory function.
  stores : List (Nat × Nat) := []
  accesses : List Access := []
  result : Option Nat := none
  failed : Bool := false
  deriving Inhabited

def word (n : Nat) : Nat := n % 4294967296

def byteAt (initial : Nat → Nat) (s : State) (a : Nat) : Nat :=
  match s.stores.find? (fun p => p.1 == a) with
  | some p => p.2
  | none => initial a

def readLE (initial : Nat → Nat) (s : State) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => byteAt initial s a + 256 * readLE initial s (a+1) n

def writeLE (s : State) (a v : Nat) : Nat → State
  | 0 => s
  | n+1 => writeLE {s with stores := (a, v % 256) :: s.stores} (a+1) (v/256) n

def memCopy (initial : Nat → Nat) (snapshot : State) (s : State) (dst src : Nat) : Nat → State
  | 0 => s
  | n+1 => memCopy initial snapshot
      {s with stores := (dst, byteAt initial snapshot src) :: s.stores} (dst+1) (src+1) n

def memFill (s : State) (dst v : Nat) : Nat → State
  | 0 => s
  | n+1 => memFill {s with stores := (dst, v % 256) :: s.stores} (dst+1) v n

def jump (s : State) (depth : Nat) : State :=
  match s.labels[depth]? with
  | none => {s with failed := true}
  | some l => {s with pc := l.target, stack := s.stack.drop (s.stack.length - l.height), labels := s.labels.drop (depth + if l.isLoop then 0 else 1)}

def bin (s : State) (f : Nat → Nat → Nat) : State :=
  match s.stack with
  | b :: a :: rest => {s with stack := f a b :: rest}
  | _ => {s with failed := true}

def step (code : Code) (initial : Nat → Nat) (s : State) : State := Id.run do
  let t := {s with pc := s.pc + 1}
  match fetch code s.pc with
  | none => return {s with failed := true}
  | some op =>
    match op with
    | .block loop ending => return {t with labels :=
        ⟨if loop then s.pc+1 else ending+1, s.stack.length, loop⟩ :: s.labels}
    | .end => return {t with labels := s.labels.drop 1}
    | .br d => return jump t d
    | .brIf d =>
      match s.stack with
      | v :: rest => return (if v == 0 then {t with stack := rest}
          else jump {t with stack := rest} d)
      | _ => return {t with failed := true}
    | .const v => return {t with stack := v :: s.stack}
    | .get i => return {t with stack := s.locals[i]! :: s.stack}
    | .set i | .tee i =>
      match s.stack with
      | v :: rest => return {t with locals := s.locals.set! i v, stack := match op with | .tee _ => s.stack | _ => rest}
      | _ => return {t with failed := true}
    | .add => return bin t (fun a b => word (a+b))
    | .sub => return bin t (fun a b => word (a+4294967296-b))
    | .and => return bin t Nat.land
    | .shr => return bin t (fun a b => a / 2^(b%32))
    | .eq => return bin t (fun a b => if a == b then 1 else 0)
    | .ne => return bin t (fun a b => if a != b then 1 else 0)
    | .gt => return bin t (fun a b => if a > b then 1 else 0)
    | .ge => return bin t (fun a b => if a ≥ b then 1 else 0)
    | .lt => return bin t (fun a b => if a < b then 1 else 0)
    | .le => return bin t (fun a b => if a ≤ b then 1 else 0)
    | .eqz =>
      match s.stack with
      | a :: rest => return {t with stack := (if a == 0 then 1 else 0) :: rest}
      | _ => return {t with failed := true}
    | .select =>
      match s.stack with
      | c :: b :: a :: rest => return {t with stack := (if c == 0 then b else a) :: rest}
      | _ => return {t with failed := true}
    | .load w off =>
      match s.stack with
      | a :: rest =>
        if a+off+w > 2097152 then return {t with failed := true}
        return {t with stack := readLE initial s (a+off) w :: rest, accesses := ⟨false, a+off, w⟩ :: s.accesses}
      | _ => return {t with failed := true}
    | .store w off =>
      match s.stack with
      | v :: a :: rest =>
        if a+off+w > 2097152 then return {t with failed := true}
        return writeLE {t with stack := rest, accesses := ⟨true, a+off, w⟩ :: s.accesses} (a+off) v w
      | _ => return {t with failed := true}
    | .copy =>
      match s.stack with
      | n :: src :: dst :: rest =>
        if src+n > 2097152 || dst+n > 2097152 then return {t with failed := true}
        return memCopy initial s {t with stack := rest, accesses := ⟨false, src, n⟩ :: ⟨true, dst, n⟩ :: s.accesses} dst src n
      | _ => return {t with failed := true}
    | .fill =>
      match s.stack with
      | n :: v :: dst :: rest =>
        if dst+n > 2097152 then return {t with failed := true}
        return memFill {t with stack := rest, accesses := ⟨true, dst, n⟩ :: s.accesses} dst v n
      | _ => return {t with failed := true}
    | .ret =>
      match s.stack with
      | a :: _ => return {t with result := some a}
      | _ => return {t with failed := true}
    -- Calls in this function lead to panic handlers. They are deliberately unsupported;
    -- no successful check below can silently pass through one.
    | .call _ | .trap => return {t with failed := true}

def run (code : Code) (initial : Nat → Nat) : Nat → State → State
  | 0, s => s
  | fuel+1, s => if s.failed || s.result.isSome then s
      else run code initial fuel (step code initial s)

def start (src dst n cap : Nat) : State :=
  {locals := ⟨[src, dst, n, cap, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩}

end Verification
