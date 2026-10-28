import Proofs.Wasm
import Proofs.Format

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Results
open Wasm

structure Case where
  name : String
  input : List Nat
  capacity : Nat
  result : Nat
  output : List Nat
  src : Nat := 131072
  dst : Nat := 196608
  deriving Repr

def fill (mem : Memory) (start : Nat) (bytes : List Nat) : Memory :=
  (bytes.zipIdx).foldl (fun m (b, i) => put m (start + i) b) mem

def initial (c : Case) : Memory :=
  fill (fill (fill (fun _ => 0) 65536 Artifact.table)
    c.dst (List.replicate c.capacity 165)) c.src c.input

def within (addr start size : Nat) : Bool := start ≤ addr && addr < start + size

def safe (src dst size capacity : Nat) (a : Access) : Bool :=
  (List.range a.size).all fun i =>
    let addr := a.addr + i
    addr < 131072 || (within addr dst capacity ||
      (!a.write && within addr src size))

def observe (fuel : Nat) (c : Case) : Option (List Nat × List Nat × Bool) := do
  let s ← invoke fuel c.src c.dst c.input.length c.capacity (initial c)
  pure (s.stack, (List.range c.output.length).map (fun i => s.mem (c.dst + i)),
    s.accesses.all (safe c.src c.dst c.input.length c.capacity))

def cases : List Case := [
  ⟨"empty-zero-capacity", [0], 0, 0, [], 131072, 196608⟩,
  ⟨"empty-positive-capacity", [0], 1, 0, [], 131072, 196608⟩,
  ⟨"missing-input", [], 1, 4294967295, [], 131072, 196608⟩,
  ⟨"missing-input-zero-capacity", [], 0, 4294967295, [], 131072, 196608⟩,
  ⟨"literal", [16, 65], 1, 1, [65], 131072, 196608⟩,
  ⟨"five-literals", [80, 65, 66, 67, 68, 69], 5, 5, [65,66,67,68,69], 131072, 196608⟩,
  ⟨"overlap-offset-one", [20,65,1,0,80,66,67,68,69,70], 14, 14,
    [65,65,65,65,65,65,65,65,65,66,67,68,69,70], 131072,196608⟩,
  ⟨"offset-zero", [4,0,0,80,66,67,68,69,70], 13, 13,
    [0,0,0,0,0,0,0,0,66,67,68,69,70], 131072,196608⟩,
  ⟨"invalid-offset", [0,1,0,80,66,67,68,69,70], 13, 4294967292,
    [],131072,196608⟩,
  ⟨"literal-too-large", [16,65], 0, 4294967295, [],131072,196608⟩,
  ⟨"truncated-literals", [32,65], 2, 4294967294, [],131072,196608⟩,
  ⟨"literal-at-memory-end", [16,65], 1, 1, [65],2097150,131072⟩,
  ⟨"output-at-memory-end", [16,65], 1, 1, [65],131072,2097151⟩,
  ⟨"zero-capacity-nonzero-token", [1],0,4294967295,[],131072,2097151⟩,
  ⟨"fifteen-literals", [240,0] ++ List.range 15,15,15,List.range 15,131072,196608⟩,
  ⟨"sixteen-literals", [240,1] ++ List.range 16,16,16,List.range 16,131072,196608⟩,
  ⟨"long-match", [31,65,1,0,0,80,66,67,68,69,70],25,25,
    List.replicate 20 65 ++ [66,67,68,69,70],131072,196608⟩,
  ⟨"shortcut-literal-and-match", [128] ++ List.range 8 ++ [8,0,192] ++ List.range 12,
    64,24,List.range 8 ++ List.range 4 ++ List.range 12,131072,196608⟩,
  ⟨"long-literal-extension", [240,255,0] ++ List.replicate 270 65,
    270,270,List.replicate 270 65,131072,196608⟩]

def passes (c : Case) : Bool :=
  observe 5000 c == some ([c.result], c.output, true) &&
    (c.result ≥ 2147483648 || (c.result ≤ c.capacity && c.result == c.output.length))

theorem checked_cases : cases.all passes = true := by decide +kernel

/- Every successful case also has the stated content under the R3 grammar:
   offset zero allowed, end conditions relaxed. -/
theorem successful_cases_parse :
    cases.all (fun c => c.result ≥ 2147483648 ||
      Format.decode true false c.input == some c.output) = true := by decide +kernel

/- The strict-format subset supplies finite R2 instances. -/
def validCases : List Case := cases.filter fun c =>
  Format.decode false true c.input == some c.output && c.result < 2147483648

theorem strict_case_count : validCases.length = 12 := by decide +kernel

#print axioms checked_cases
#print axioms successful_cases_parse
#print axioms strict_case_count

end Results
