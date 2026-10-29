import Proofs.Artifact
import Proofs.Format

set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace Results
open Wasm

def observe (s : Option State) : Option (Nat × Bool × List (Nat × Nat) × List (Nat × Nat)) := do
  let s ← s
  let r ← s.result
  pure (r, s.safe, s.reads, s.mem.writes)

/-- Universal subcase of R1: zero input, any addresses, capacity and initial memory.
    Returns i32 -1 without any memory operation. Not a proof for n > 0. -/
theorem zero_input (src dst cap : Nat) (m : Nat → Nat) :
    observe (run 6 (initial Artifact.program ⟨src, dst, 0, cap⟩ m)) =
      some (4294967295, true, [], []) := by rfl

structure Case where
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  strict : Bool := true

def cases : List Case := [
  ⟨[0], 0, some [], true⟩,
  ⟨[16, 97], 1, some [97], true⟩,
  ⟨[19, 97, 1, 0, 80, 98, 99, 100, 101, 102], 13,
    some (List.replicate 8 97 ++ [98, 99, 100, 101, 102]), true⟩,
  ⟨[64, 97, 98, 99, 100, 4, 0, 240, 0] ++ List.replicate 15 120, 64,
    some ([97,98,99,100,97,98,99,100] ++ List.replicate 15 120), true⟩,
  ⟨[19, 97, 1, 0, 240, 0] ++ List.replicate 15 120, 64,
    some (List.replicate 8 97 ++ List.replicate 15 120), true⟩,
  ⟨[240, 0] ++ List.replicate 15 98, 15, some (List.replicate 15 98), true⟩,
  ⟨[16, 97, 0, 0], 64, none, false⟩,
  ⟨[16, 97, 0, 0] ++ List.replicate 20 0, 64, none, false⟩,
  ⟨[16, 97, 2, 0], 64, none, false⟩,
  ⟨[240, 255], 64, none, false⟩,
  ⟨[16, 97, 1, 0, 0], 5, some (List.replicate 5 97), false⟩]

def memory (input : List Nat) (p : Nat) : Nat :=
  if 131072 ≤ p && p < 131072 + input.length then input[p-131072]! else 165

/-- Fixed source/destination regions are disjoint, in caller memory, and contain bytes. -/
theorem cases_valid_buffers : cases.all (fun c =>
    c.input.length ≤ 131072 && c.cap ≤ 1835008 && c.input.all (· < 256)) = true := by decide

def execution (c : Case) : Option State :=
  run 2000 (initial Artifact.program ⟨131072, 262144, c.input.length, c.cap⟩ (memory c.input))

def check (c : Case) : Bool :=
  match execution c with
  | none => false
  | some s => s.safe && Format.decode c.strict c.input == c.expected &&
    match c.expected with
    | none => s.result == some 4294967295
    | some out => s.result == some out.length && out.length ≤ c.cap &&
      (List.range out.length).map (fun i => byte s.mem (262144+i)) == out

/-- Finite artifact executions only; this does not quantify over all legal buffers or blocks. -/
theorem certified_cases : cases.all check = true := by decide

end Results
