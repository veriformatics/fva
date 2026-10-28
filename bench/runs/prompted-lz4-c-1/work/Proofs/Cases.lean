import Proofs.Artifact
import Proofs.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Verification
open Wasm
structure Case where
  input : Bytes
  cap : Nat
  expected : Nat
  src : Nat := 131072
  dst : Nat := 1048576
  fill : Nat := 165
  deriving Repr

-- Caller memory is deliberately nonzero, including the initially unwritten output.
def initial (c : Case) : Mem := fun p =>
  if c.src ≤ p && p < c.src+c.input.length then (c.input[p-c.src]?).getD 0
  else if 65536 ≤ p && p < 65600 then (Artifact.dataBytes[p-65536]?).getD 0
  else if 131072 ≤ p && p < 2097152 then c.fill else 0

def legal (c : Case) : Bool :=
  131072 ≤ c.src && c.src+c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst+c.cap ≤ 2097152 &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src)

def execute (c : Case) :=
  run Artifact.functions 1000 (start Artifact.functions (initial c) c.src c.dst c.input.length c.cap)

def inside (p lo len : Nat) : Bool := lo ≤ p && p < lo+len
def safeAccess (c : Case) (a : Access) : Bool := (List.range a.width).all fun k =>
  let p := a.address+k
  p < 131072 || (inside p c.dst c.cap || (!a.write && inside p c.src c.input.length))

def outputIs (c : Case) (r : Nat) (s : State) (out : Bytes) : Bool :=
  r == out.length && (List.range r).all (fun k => s.mem (c.dst+k) == (out[k]?).getD 0)

def checks (c : Case) : Bool := legal c && (match execute c with
  | none => false
  | some (r,s) => r == c.expected && s.trace.all (safeAccess c) &&
    (match LZ4.decode c.input with
    | none => r ≥ 2147483648
    | some d =>
      -- R2 on this input whenever all its antecedents hold.
      (!(d.conforming && d.content.length ≤ c.cap && (0 < c.cap || c.input == [0])) ||
        outputIs c r s d.content) &&
      -- R3 on this input whenever the return value is nonnegative.
      (r ≥ 2147483648 || (r ≤ c.cap && outputIs c r s d.content))))

-- These are examples, not a bound on the inputs quantified over in README.md.
def cases : List Case := [
  ⟨[],32,4294967295,131072,1048576,165⟩,
  ⟨[0],0,0,131072,1048576,165⟩,
  ⟨[0],32,0,131072,1048576,165⟩,
  ⟨[1],0,4294967295,131072,1048576,165⟩,
  ⟨[15],32,0,131072,1048576,165⟩,
  ⟨[16,65],1,1,131072,1048576,165⟩,
  ⟨[80,65,66,67,68,69],5,5,131072,1048576,165⟩,
  ⟨[240,0] ++ List.range 15,15,15,131072,1048576,165⟩,
  ⟨[19,65,1,0,80,66,67,68,69,70],13,13,131072,1048576,165⟩,
  ⟨[19,65,1,0,80,66,67,68,69,70],64,13,131072,1048576,165⟩,
  ⟨[31,65,1,0,1,80,66,67,68,69,70],26,26,131072,1048576,165⟩,
  ⟨[3,0,0,80,66,67,68,69,70],12,12,131072,1048576,165⟩,
  ⟨[3,0,0,80,66,67,68,69,70],64,12,131072,1048576,165⟩,
  ⟨[3,1,0,80,66,67,68,69,70],64,4294967292,131072,1048576,165⟩,
  ⟨[16,65],1,1,2097150,131072,165⟩,
  ⟨[16,65],1,1,131072,2097151,165⟩
]

-- A summary retains exactly the user-visible return value and all memory accesses.
def observation (o : Option (Nat × State)) : Option (Nat × List Access) :=
  o.map fun (r,s) => (r,s.trace)

theorem no_input (mem : Mem) :
    observation (run Artifact.functions 32
      (start Artifact.functions mem 131072 1048576 0 32)) = some (4294967295,[]) := by rfl

theorem zero_capacity (mem : Mem) :
    observation (run Artifact.functions 32
      (start Artifact.functions mem 131072 1048576 1 0)) =
      some ((if load mem 131072 1 == 0 then 0 else 4294967295),[⟨false,131072,1⟩]) := by rfl

-- The finite aggregate theorem is Certificates.checked_cases.
end Verification
