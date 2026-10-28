import Proofs.Artifact
import Proofs.Format

namespace Verification.Cases
open Wasm

structure Case where
  name : String
  input : List Nat
  capacity : Nat
  expectedReturn : Nat -- unsigned i32 representation
  expected : List Nat
  valid : Bool
  src : Nat := 131072
  dst : Nat := 262144
  deriving Repr, DecidableEq, Inhabited

def cases : List Case := [
  ⟨"empty_zero_capacity", [0], 0, 0, [], true, 131072, 262144⟩,
  ⟨"empty_positive_capacity", [0], 1, 0, [], true, 131072, 262144⟩,
  ⟨"no_input", [], 1, 4294967295, [], false, 131072, 262144⟩,
  ⟨"literal_one", [16, 65], 1, 1, [65], true, 131072, 262144⟩,
  ⟨"literal_one_no_capacity", [16, 65], 0, 4294967295, [], false, 131072, 262144⟩,
  ⟨"overlap_offset_one", [19, 65, 1, 0, 80, 66, 67, 68, 69, 70],
    13, 13, [65,65,65,65,65,65,65,65,66,67,68,69,70], true, 131072, 262144⟩,
  ⟨"offset_zero", [3, 0, 0, 80, 65, 66, 67, 68, 69],
    12, 12, [0,0,0,0,0,0,0,65,66,67,68,69], false, 131072, 262144⟩,
  ⟨"literal_extension", [240,0,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79],
    15, 15, [65,66,67,68,69,70,71,72,73,74,75,76,77,78,79], true, 131072, 262144⟩,
  ⟨"shortcut", [132,65,66,67,68,69,70,71,72,8,0,128,73,74,75,76,77,78,79,80],
    64, 24, [65,66,67,68,69,70,71,72,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80],
    true, 131072, 262144⟩,
  ⟨"truncated_extension", [240], 64, 4294967294, [], false, 131072, 262144⟩,
  ⟨"offset_before_output", [0,1,0,80,65,66,67,68,69], 64, 4294967292, [], false, 131072, 262144⟩,
  ⟨"literal_at_memory_end", [16,90], 1, 1, [90], true, 2097150, 131072⟩
]

def preconditions (c : Case) : Bool :=
  c.src ≥ 131072 && c.src + c.input.length ≤ memorySize &&
  c.dst ≥ 131072 && c.dst + c.capacity ≤ memorySize &&
  (c.src + c.input.length ≤ c.dst || c.dst + c.capacity ≤ c.src)

-- Nonzero initial destination detects accidental dependence on stale bytes.
def initialMemory (c : Case) : Memory :=
  putBytes (putBytes Artifact.initialData c.dst (List.replicate c.capacity 165)) c.src c.input

def execute (c : Case) : Option Result :=
  invoke Artifact.program 12000 2 [c.src, c.dst, c.input.length, c.capacity] (initialMemory c)

def inside (a base size : Nat) : Bool := base ≤ a && a < base + size

-- Account for every byte of every load and store, including failed calls.
def accessOK (c : Case) (e : Access) : Bool :=
  (List.range e.width).all fun j =>
    let a := e.address + j
    if inside a 131072 (memorySize - 131072) then
      if e.write then inside a c.dst c.capacity
      else inside a c.src c.input.length || inside a c.dst c.capacity
    else true

def output (c : Case) (r : Result) (len : Nat) : List Nat :=
  (List.range len).map fun j => byte r.mem (c.dst + j)

def r1 (c : Case) (r : Result) : Bool := r.accesses.all (accessOK c)

def r2 (c : Case) (r : Result) : Bool :=
  if c.valid then
    Format.validIndependent c.input c.expected &&
    (c.capacity ≥ 1 || c.input == [0]) &&
    c.expected.length ≤ c.capacity &&
    r.value == c.expected.length && output c r r.value == c.expected
  else true

def r3 (c : Case) (r : Result) : Bool :=
  if r.value < 2147483648 then
    r.value ≤ c.capacity &&
    match Format.decode true c.input with
    | none => false
    | some d => r.value == d.content.length && output c r r.value == d.content
  else true

def check (c : Case) : Bool :=
  preconditions c &&
  match execute c with
  | none => false
  | some r => r.value == c.expectedReturn && r1 c r && r2 c r && r3 c r

-- The declarations below are checked by the Lean kernel, without native_decide.
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem empty_zero_capacity : check cases[0]! = true := by decide
theorem empty_positive_capacity : check cases[1]! = true := by decide
theorem no_input : check cases[2]! = true := by decide
theorem literal_one : check cases[3]! = true := by decide
theorem literal_one_no_capacity : check cases[4]! = true := by decide
theorem overlap_offset_one : check cases[5]! = true := by decide
theorem offset_zero : check cases[6]! = true := by decide
theorem literal_extension : check cases[7]! = true := by decide
theorem shortcut : check cases[8]! = true := by decide
theorem truncated_extension : check cases[9]! = true := by decide
theorem offset_before_output : check cases[10]! = true := by decide
theorem literal_at_memory_end : check cases[11]! = true := by decide

end Verification.Cases
