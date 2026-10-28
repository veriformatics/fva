import Proofs.Wasm

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Prefix
open Wasm

/- Suffix is obtained from the parsed artifact, not transcribed source. -/
def suffix : List Instr :=
  match program 2 with
  | some f =>
    match f.code[2]? with
    | some (Instr.block _ body) => body.drop 11
    | _ => []
  | _ => []

def zeroCapacityBody : List Instr := [
  .op 32 3 0, .op 13 0 0, .op 32 2 0, .op 65 1 0, .op 71 0 0,
  .op 13 1 0, .op 65 4294967295 0, .op 65 0 0, .op 32 0 0,
  .op 45 0 0, .op 27 0 0, .op 15 0 0]

def decoder : Func := ⟨4, 15, [
  .op 65 4294967295 0, .op 33 4 0,
  .block false ([.op 32 0 0, .op 69 0 0, .op 13 0 0,
    .op 32 3 0, .op 65 0 0, .op 72 0 0, .op 13 0 0,
    .block false zeroCapacityBody, .op 32 2 0, .op 69 0 0,
    .op 13 0 0] ++ suffix), .op 32 4 0]⟩

theorem decoder_is_artifact : program 2 = some decoder := by rfl

def project (s : State) : List Nat × List Access × Memory :=
  (s.stack, s.accesses, s.mem)

/- Every natural-valued memory is permitted, and is interpreted bytewise. -/
theorem zero_capacity (src dst size : Nat) (mem : Memory)
    (hs : src ≠ 0) (hb : src < 2097152) :
    (invoke 100 src dst size 0 mem).map project =
      some ([if size == 1 && mem src % 256 == 0 then 0 else 4294967295],
        if size == 1 then [⟨false, src, 1⟩] else [], mem) := by
  by_cases hsize : size = 1
  · subst size
    simp [invoke, decoder_is_artifact, decoder, zeroCapacityBody, exec,
      binary, signed, project, readLE, hs, Nat.not_lt.mpr (Nat.succ_le_of_lt hb)]
  · simp [invoke, decoder_is_artifact, decoder, zeroCapacityBody, exec,
      binary, signed, project, hsize]

theorem zero_input (src dst capacity : Nat) (mem : Memory) :
    (invoke 100 src dst 0 capacity mem).map project =
      some ([4294967295], [], mem) := by
  by_cases hz : capacity = 0
  · subst capacity
    simp [invoke, decoder_is_artifact, decoder, zeroCapacityBody, exec,
      binary, signed, project]
  · simp [invoke, decoder_is_artifact, decoder, zeroCapacityBody, exec,
      binary, signed, project, hz]

#print axioms decoder_is_artifact
#print axioms zero_capacity
#print axioms zero_input
end Prefix
