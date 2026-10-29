import Proofs.Artifact
import Proofs.Format
import Proofs.Samples
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Verification
open Wasm

def artifactMemory : Memory := fun a =>
  Artifact.data.foldl (fun value segment =>
    if segment.1 ≤ a ∧ a < segment.1 + segment.2.length then
      (segment.2[a-segment.1]?).getD 0 else value) 0

def inputMemory (input : List Nat) : Memory := fun a =>
  if 131072 ≤ a ∧ a < 131072 + input.length then
    (input[a-131072]?).getD 0 else artifactMemory a

def execute (c : Samples.Case) : State :=
  run Artifact.code c.fuel (initial Artifact.localCount 131072 262144 c.input.length c.cap
    (inputMemory c.input))

/-- Exact return, content and R1 trace assertions for a completed state. -/
def observed (c : Samples.Case) (s : State) : Bool :=
  s.status == .returned c.result &&
  bytesAt s.mem 262144 c.output.length == c.output &&
  s.events.all (eventSafe 131072 262144 c.input.length c.cap)

def agrees (c : Samples.Case) : Bool := observed c (execute c)

theorem agrees_of_execution (c : Samples.Case) (s : State)
    (execution : execute c = s) (observation : observed c s = true) : agrees c = true :=
  Eq.trans (congrArg (observed c) execution) observation

/-- All sample buffers meet README's address and disjointness preconditions. -/
def admissible (c : Samples.Case) : Bool :=
  131072 + c.input.length ≤ 262144 && 262144 + c.cap ≤ 2097152 &&
  c.output.length ≤ c.cap && c.input.all (· < 256)

/-- Positive cases satisfy the independent format specification, with a single
    explicitly named relaxed-end case. Error results make no format claim. -/
def formatAgrees (c : Samples.Case) : Bool :=
  if c.result = 4294967295 then true else
  c.result == c.output.length && LZ4.relaxedDecode c.input c.output &&
    (c == Samples.relaxed_end || LZ4.validIndependent c.input c.output)

/-- Universal, artifact-specific R1 subcase: zero input reads/writes nothing. -/
theorem zero_input (src dst cap : Nat) (m : Memory) :
    let s := run Artifact.code 5 (initial Artifact.localCount src dst 0 cap m)
    s.status = .returned 4294967295 ∧ s.mem = m ∧ s.events = [] := by
  let s0 := initial Artifact.localCount src dst 0 cap m
  let fs : List Frame := [⟨6, false, []⟩]
  let s1 : State := { s0 with pc := 1, frames := fs }
  let s2 : State := { s0 with pc := 2, frames := fs, stack := [0] }
  let s3 : State := { s0 with pc := 3, frames := fs }
  let s4 : State := { s0 with pc := 4, frames := fs, stack := [4294967295] }
  let s5 : State := { s4 with status := .returned 4294967295 }
  have h0 : run Artifact.code 1 s0 = s1 := rfl
  have h1 : run Artifact.code 1 s1 = s2 := rfl
  have h2 : run Artifact.code 1 s2 = s3 := rfl
  have h3 : run Artifact.code 1 s3 = s4 := rfl
  have h4 : run Artifact.code 1 s4 = s5 := rfl
  have h : run Artifact.code 5 s0 = s5 :=
    run_join _ 1 4 s0 s1 s5 h0
      (run_join _ 1 3 s1 s2 s5 h1
        (run_join _ 1 2 s2 s3 s5 h2
          (run_join _ 1 1 s3 s4 s5 h3 h4)))
  change (run Artifact.code 5 s0).status = .returned 4294967295 ∧
    (run Artifact.code 5 s0).mem = m ∧ (run Artifact.code 5 s0).events = []
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

-- Each equality is checked by kernel reduction, with no native_decide oracle.
theorem buffers_admissible : Samples.all.all admissible = true := rfl
theorem samples_format : Samples.all.all formatAgrees = true := rfl
end Verification
