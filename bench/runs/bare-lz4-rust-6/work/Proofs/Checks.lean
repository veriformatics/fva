import Proofs.Artifact
import Proofs.LZ4

namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def initialState (src dst n cap : Nat) (mem : Memory) : State :=
  { locals := #[src, dst, n, cap] ++ Array.replicate 24 0, mem := mem }

structure Case where
  name : String
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  -- 0: invalid syntax, 1: full format, 2: only end conditions relaxed.
  format : Nat
  src : Nat := 131072
  dst : Nat := 1048576
  deriving Repr

def allowed (c : Case) (a : Access) : Bool :=
  a.width == 0 ||
    (c.dst ≤ a.address && a.address + a.width ≤ c.dst + c.cap) ||
    (!a.write && c.src ≤ a.address && a.address + a.width ≤ c.src + c.input.length)

def preconditions (c : Case) : Bool :=
  c.src ≥ 131072 && c.dst ≥ 131072 &&
  c.src + c.input.length ≤ 2097152 && c.dst + c.cap ≤ 2097152 &&
  (c.src + c.input.length ≤ c.dst || c.dst + c.cap ≤ c.src) &&
  c.input.all (· < 256)

def caseMemory (c : Case) : Memory :=
  ⟨fun addr => if c.src ≤ addr && addr < c.src + c.input.length then
    c.input[addr - c.src]! else 165, []⟩

def checkCase (c : Case) : Bool := Id.run do
  if !preconditions c then return false
  let spec := reference c.input
  let syntaxOK := match spec with
    | none => c.format == 0
    | some d => if c.format == 1 then endConditions d
                else c.format == 2 && !endConditions d
  if !syntaxOK then return false
  match run program 20000 (initialState c.src c.dst c.input.length c.cap (caseMemory c)) with
  | .returned r s =>
    if !s.accesses.all (allowed c) then return false
    match c.expected with
    | none => return r == 4294967295
    | some expected =>
      let specOK := match spec with
        | some d => d.bytes == expected
        | none => false
      return specOK && r == expected.length && r ≤ c.cap &&
        (List.range r).all (fun i => s.mem.byte (c.dst + i) == expected[i]!)
  | _ => return false

end Verification
