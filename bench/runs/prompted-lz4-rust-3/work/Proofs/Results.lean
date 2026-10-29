import Proofs.Wasm
import Proofs.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Results

-- Addresses and lengths are byte offsets, with half-open intervals.
def within (a n base size : Nat) : Bool := base ≤ a && a+n ≤ base+size

def allowed (src dst n cap : Nat) (e : Wasm.Event) : Bool :=
  if e.width == 0 then true else
  (List.range e.width).all fun j =>
    let a := e.address+j
    a < 131072 ||
      (if e.write then within a 1 dst cap else within a 1 src n || within a 1 dst cap)

structure Case where
  input : List Nat
  cap : Nat
  result : Nat
  output : List Nat
  valid : Bool
  deriving Repr

def cases : List Case := [
  ⟨[], 0, Wasm.word-1, [], false⟩,
  ⟨[0], 0, 0, [], true⟩,
  ⟨[15], 0, 0, [], true⟩,
  ⟨[16,65], 1, 1, [65], true⟩,
  ⟨[32,65,66], 2, 2, [65,66], true⟩,
  ⟨[48,65,66,67], 3, 3, [65,66,67], true⟩,
  ⟨[64,65,66,67,68], 4, 4, [65,66,67,68], true⟩,
  ⟨[80,65,66,67,68,69], 5, 5, [65,66,67,68,69], true⟩,
  ⟨[240,0] ++ List.range 15, 15, 15, List.range 15, true⟩,
  ⟨[240,1] ++ List.range 16, 16, 16, List.range 16, true⟩,
  ⟨[19,65,1,0,80,66,67,68,69,70], 13, 13,
    List.replicate 8 65 ++ [66,67,68,69,70], true⟩,
  ⟨[30,65,1,0,240,0] ++ List.range 15, 40, 34,
    List.replicate 19 65 ++ List.range 15, true⟩,
  ⟨[131] ++ List.range 8 ++ [8,0,80,20,21,22,23,24], 64, 20,
    List.range 8 ++ List.range 7 ++ [20,21,22,23,24], true⟩,
  ⟨[38,65,66,2,0,80,20,21,22,23,24], 17, 17,
    List.flatten (List.replicate 6 [65,66]) ++ [20,21,22,23,24], true⟩,
  ⟨[31,65,1,0,0,80,20,21,22,23,24], 25, 25,
    List.replicate 20 65 ++ [20,21,22,23,24], true⟩,
  ⟨[16,65,1,0,0], 5, 5, List.replicate 5 65, false⟩,
  ⟨[16,65,0,0,80,20,21,22,23,24], 32, Wasm.word-1, [], false⟩,
  ⟨[0,1,0], 32, Wasm.word-1, [], false⟩,
  ⟨[0,1], 32, Wasm.word-1, [], false⟩,
  ⟨[32,65], 32, Wasm.word-1, [], false⟩,
  ⟨[240], 32, Wasm.word-1, [], false⟩,
  ⟨[240,255], 32, Wasm.word-1, [], false⟩,
  ⟨[32,65,66], 1, Wasm.word-1, [], false⟩,
  ⟨[16,65,1,0], 4, Wasm.word-1, [], false⟩]

def src : Nat := 131072
def dst : Nat := 262144

def memory (input : List Nat) : Nat → Nat := fun a =>
  if src ≤ a ∧ a < src+input.length then input[a-src]?.getD 0 else 204

def observe (c : Case) : Option (Nat × Wasm.State) :=
  Wasm.run 5000 (Wasm.initial src dst c.input.length c.cap (memory c.input))

def r1Case (c : Case) : Bool :=
  match observe c with
  | none => false
  | some (_, s) => s.events.all (allowed src dst c.input.length c.cap)

def r2Case (c : Case) : Bool :=
  if !c.valid then true else
    match LZ4.decode c.input, observe c with
    | some d, some (r,s) =>
      LZ4.endConditions d && d.output.length ≤ c.cap &&
      r == d.output.length &&
      (List.range r).map (fun j => s.mem (dst+j)) == d.output
    | _, _ => false

-- This implication is meaningful for every successful observed return, including
-- the deliberately accepted block that violates the end-of-block conditions.
def r3Case (c : Case) : Bool :=
  match observe c with
  | none => false
  | some (r,s) =>
    if r ≥ 2147483648 then true else
      match LZ4.decode c.input with
      | none => false
      | some d => r ≤ c.cap && r == d.output.length &&
        (List.range r).map (fun j => s.mem (dst+j)) == d.output

def expectedCase (c : Case) : Bool :=
  match observe c with
  | none => false
  | some (r,s) => r == c.result &&
    (List.range c.output.length).map (fun j => s.mem (dst+j)) == c.output

-- Valid, disjoint caller buffers for every case in the finite suite.
def interfaceCase (c : Case) : Bool :=
  src ≥ 131072 && src+c.input.length ≤ dst &&
  dst ≥ 131072 && dst+c.cap ≤ 2097152 &&
  c.input.all (· < 256)

theorem empty_input (src dst cap : Nat) (mem : Nat → Nat) :
    (Wasm.run 5 (Wasm.initial src dst 0 cap mem)).map
      (fun (r,s) => (r, s.mem, s.events)) = some (Wasm.word-1, mem, []) := by
  rfl

theorem interface_cases : cases.all interfaceCase = true := by decide +kernel
theorem expected_cases : cases.all expectedCase = true := by decide +kernel
theorem r1_cases : cases.all r1Case = true := by decide +kernel
theorem r2_cases : cases.all r2Case = true := by decide +kernel
theorem r3_cases : cases.all r3Case = true := by decide +kernel

end Results
