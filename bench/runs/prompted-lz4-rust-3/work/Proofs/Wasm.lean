import Proofs.Program
/- A partial interpreter of the decoded shipped function. Unsupported instructions,
   traps and exhausted fuel produce none. Calls are unsupported. Only witnessed
   successful executions are claimed. Words are unsigned bit patterns. -/
namespace Wasm

structure Frame where
  target : List Instr
  continuation : List Instr
  isLoop : Bool
  height : Nat

structure Event where
  write : Bool
  address : Nat
  width : Nat
  deriving DecidableEq, Repr

structure State where
  pc : List Instr
  locals : List Nat
  stack : List Nat := []
  frames : List Frame := []
  mem : Nat → Nat
  events : List Event := []

def load (mem : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | a, n+1 => mem a % 256 + 256 * load mem (a+1) n

def store (mem : Nat → Nat) : Nat → Nat → Nat → (Nat → Nat)
  | _, 0, _ => mem
  | a, n+1, v => store (fun k => if k == a then v % 256 else mem k) (a+1) n (v/256)

-- memory.copy reads its entire source from the pre-instruction memory (memmove).
def copy (mem : Nat → Nat) (dst src n : Nat) : Nat → Nat :=
  fun a => if dst ≤ a ∧ a < dst+n then mem (src+a-dst) else mem a

def fill (mem : Nat → Nat) (dst v n : Nat) : Nat → Nat :=
  fun a => if dst ≤ a ∧ a < dst+n then v % 256 else mem a

def branch (s : State) (depth : Nat) : Option State := do
  let frame ← s.frames[depth]?
  if frame.height > s.stack.length then none else
    pure {s with pc := frame.target,
                 stack := s.stack.drop (s.stack.length-frame.height),
                 frames := s.frames.drop (depth + if frame.isLoop then 0 else 1)}

inductive Step where
  | next (state : State)
  | done (value : Nat) (state : State)

-- No instruction outside the cases below is silently treated as a no-op.
def step (s : State) : Option Step := do
  match s.pc with
  | [] =>
    match s.frames with
    | [] =>
      let v :: _ := s.stack | none
      pure (.done v s)
    | frame :: frames =>
      if frame.height > s.stack.length then none else
        pure (.next {s with pc := frame.continuation, frames, stack := s.stack.drop (s.stack.length-frame.height)})
  | .block body :: rest =>
    pure (.next {s with pc := body, frames := ⟨rest, rest, false, s.stack.length⟩ :: s.frames})
  | .loop body :: rest =>
    pure (.next {s with pc := body, frames := ⟨body, rest, true, s.stack.length⟩ :: s.frames})
  | .prim op a :: rest => do
   let t := {s with pc := rest}
   match op with
   | 12 => return .next (← branch t a)
   | 13 =>
     let cond :: stack := s.stack | none
     let t := {t with stack}
     if cond == 0 then pure (.next t) else return .next (← branch t a)
   | 15 =>
     let value :: _ := s.stack | none
     pure (.done value t)
   | 27 =>
     let cond :: v2 :: v1 :: stack := s.stack | none
     pure (.next {t with stack := (if cond == 0 then v2 else v1) :: stack})
   | 32 =>
     let value ← s.locals[a]?
     pure (.next {t with stack := value :: s.stack})
   | 33 | 34 =>
     let value :: stack := s.stack | none
     if a ≥ s.locals.length then none else
       pure (.next {t with locals := s.locals.set a value,
                           stack := if op == 34 then s.stack else stack})
   | 65 => pure (.next {t with stack := a :: s.stack})
   | 69 =>
     let v :: stack := s.stack | none
     pure (.next {t with stack := (if v == 0 then 1 else 0) :: stack})
   | 70 | 71 | 73 | 75 | 77 | 79 | 106 | 107 | 113 | 118 =>
     let y :: x :: stack := s.stack | none
     let v := match op with
       | 70 => if x == y then 1 else 0
       | 71 => if x != y then 1 else 0
       | 73 => if x < y then 1 else 0
       | 75 => if x > y then 1 else 0
       | 77 => if x ≤ y then 1 else 0
       | 79 => if x ≥ y then 1 else 0
       | 106 => (x+y) % word
       | 107 => (x+word-y) % word
       | 113 => Nat.land x y
       | _ => x / 2^(y%32)
     pure (.next {t with stack := v :: stack})
   | 40 | 41 | 45 | 47 =>
     let base :: stack := s.stack | none
     let width := if op == 41 then 8 else if op == 40 then 4 else if op == 47 then 2 else 1
     if base+a+width > 2097152 then none else
       pure (.next {t with stack := load s.mem (base+a) width :: stack,
                           events := ⟨false, base+a, width⟩ :: s.events})
   | 54 | 55 | 58 | 59 =>
     let v :: base :: stack := s.stack | none
     let width := if op == 55 then 8 else if op == 54 then 4 else if op == 59 then 2 else 1
     if base+a+width > 2097152 then none else
       pure (.next {t with stack, mem := store s.mem (base+a) width v,
                           events := ⟨true, base+a, width⟩ :: s.events})
   | 266 | 267 =>
     let n :: v :: dst :: stack := s.stack | none
     if dst+n > 2097152 then none else
       if op == 266 then
         if v+n > 2097152 then none else
           pure (.next {t with stack, mem := copy s.mem dst v n, events := ⟨true, dst, n⟩ :: ⟨false, v, n⟩ :: s.events})
       else pure (.next {t with stack, mem := fill s.mem dst v n, events := ⟨true, dst, n⟩ :: s.events})
   | _ => none
 
def run : Nat → State → Option (Nat × State)
  | 0, _ => none
  | f+1, s => do
    match ← step s with
    | .done v t => pure (v, t)
    | .next t => run f t

def initial (src dst n cap : Nat) (mem : Nat → Nat) : State :=
  ⟨Artifact.program, [src, dst, n, cap] ++ List.replicate 24 0, [], [], mem, []⟩

end Wasm
