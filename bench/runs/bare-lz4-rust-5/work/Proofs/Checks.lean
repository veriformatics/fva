import Proofs.Artifact
import Proofs.Format

namespace Verification
open Wasm Artifact

structure Case where
  name : String
  input : List Nat
  cap : Nat
  result : Nat  -- i32 bit pattern, including 0xffffffff for -1
  output : List Nat := []
  sequences : List LZ4.Sequence := []
  validEnd : Bool := false
  src : Nat := 131072
  dst : Nat := 262144
  deriving Repr

def precondition (c : Case) : Bool :=
  131072 ≤ c.src && c.src < memorySize && c.src + c.input.length ≤ memorySize &&
  131072 ≤ c.dst && c.dst < memorySize && c.dst + c.cap ≤ memorySize &&
  (c.src + c.input.length ≤ c.dst || c.dst + c.cap ≤ c.src) &&
  c.input.all (· < 256)

def caseMemory (c : Case) : Memory := fun a =>
  if c.src ≤ a ∧ a < c.src + c.input.length then c.input[a - c.src]!
  else if c.dst ≤ a ∧ a < c.dst + c.cap then 165 else 0

def execution (c : Case) : Outcome :=
  run decoder 50000 (initial c.src c.dst c.input.length c.cap (caseMemory c))

def bytesAt (m : Memory) (base len : Nat) : List Nat :=
  (List.range len).map (fun i => m (base + i))

def check (c : Case) : Bool :=
  precondition c && match execution c with
  | .returned r s =>
      r == c.result &&
      s.accesses.all (permitted c.src c.dst c.input.length c.cap) &&
      -- This also justifies omitting the module's private data initializers
      -- from caseMemory: none of these executions ever accesses that region.
      s.accesses.all (fun a => 131072 ≤ a.address) &&
      (if r < 2147483648 then
        r ≤ c.cap && r == c.output.length && bytesAt s.mem c.dst r == c.output &&
        LZ4.certificate c.input c.output c.sequences &&
        (!c.validEnd || LZ4.endConditions c.output c.sequences)
       else r == 4294967295)
  | _ => false

end Verification
