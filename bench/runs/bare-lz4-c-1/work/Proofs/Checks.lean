import Proofs.Artifact
import Proofs.Format

namespace Verification
open Wasm

structure Case where
  input : List Nat
  capacity : Nat
  output : Option (List Nat) -- none means a negative result is required
  strict : Bool := false
  src : Nat := 131072
  dst : Nat := 196608
  deriving Repr

def memory (c : Case) : Memory := fun a =>
  if 65536 ≤ a ∧ a < 65600 then Artifact.staticData[a - 65536]!
  else if c.src ≤ a ∧ a < c.src + c.input.length then c.input[a - c.src]!
  else if a < 131072 then 0 else 165

def result (c : Case) : State :=
  run Artifact.program 2000 (initial (memory c) c.src c.dst c.input.length c.capacity)

def preconditions (c : Case) : Bool :=
  131072 ≤ c.src && c.src + c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst + c.capacity ≤ 2097152 &&
  (c.src + c.input.length ≤ c.dst || c.dst + c.capacity ≤ c.src) &&
  c.input.all (· < 256)

def safeTrace (c : Case) (s : State) : Bool :=
  s.trace.all fun a => decide (accessOK c.src c.dst c.input.length c.capacity a)

def check (c : Case) : Bool := Id.run do
  if !preconditions c then return false
  let s := result c
  if !safeTrace c s then return false
  let .halted r := s.status | return false
  match c.output with
  | none => return r ≥ 2147483648
  | some out =>
    if r != out.length || r > c.capacity then return false
    if (List.range r).map (fun i => s.mem (c.dst + i)) != out then return false
    let some d := LZ4Format.decode (!c.strict) c.input | return false
    return d.bytes == out && (!c.strict || LZ4Format.endOK d)

end Verification
