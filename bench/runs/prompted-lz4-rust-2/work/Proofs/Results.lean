import Proofs.Artifact
import Proofs.Format
namespace Verification
open Wasm
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def execute (src dst n cap : Nat) (mem : Memory) : State :=
  run Artifact.program 2000 (start Artifact.f7 src dst n cap mem)

-- This statement quantifies over every memory, address and capacity.
theorem empty_input (src dst cap : Nat) (mem : Memory) :
    (execute src dst 0 cap mem).status = .done 4294967295 ∧
    (execute src dst 0 cap mem).accesses = [] ∧
    (execute src dst 0 cap mem).mem = mem := by
  cbv

structure Case where
  name : String
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  valid : Bool
  src : Nat := 131072
  dst : Nat := 1048576

def initial (c : Case) : Memory := fun a =>
  if c.src ≤ a ∧ a < c.src+c.input.length then c.input[a-c.src]?.getD 0
  else if c.dst ≤ a ∧ a < c.dst+c.cap then 165
  else if 65536 ≤ a ∧ a < 65536+Artifact.dataBytes.length then
    Artifact.dataBytes[a-65536]?.getD 0
  else if a < 131072 then 0 else 90

def inside (a size base len : Nat) : Bool := base ≤ a && a+size ≤ base+len

def permitted (c : Case) (a : Access) : Bool :=
  a.addr+a.size ≤ 131072 ||
    inside a.addr a.size c.dst c.cap ||
    (!a.write && inside a.addr a.size c.src c.input.length)

def admissible (c : Case) : Bool :=
  131072 ≤ c.src && c.src+c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst+c.cap ≤ 2097152 &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src)

def outputIs (s : State) (dst : Nat) (out : List Nat) : Bool :=
  (List.range out.length).all (fun i => s.mem (dst+i) == out[i]?.getD 0)

def checkCase (c : Case) : Bool :=
  let s := execute c.src c.dst c.input.length c.cap (initial c)
  let operational := match c.expected with
    | none => s.status == .done 4294967295
    | some out => s.status == .done out.length && outputIs s c.dst out
  let spec := Format.parse c.input
  let valid := match spec with
    | none => false
    | some p => Format.endConditions p
  let r2 := match spec with
    | none => true
    | some p => !Format.endConditions p || p.content.length > c.cap ||
        (s.status == .done p.content.length && outputIs s c.dst p.content)
  let r3 := match s.status with
    | .done r => r == 4294967295 || (r ≤ c.cap && match spec with
        | none => false
        | some p => r == p.content.length && outputIs s c.dst p.content)
    | _ => false
  admissible c && operational && s.accesses.all (permitted c) &&
    (valid == c.valid) && r2 && r3

end Verification
