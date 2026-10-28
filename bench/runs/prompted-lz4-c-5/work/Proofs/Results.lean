import Proofs.Wasm
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000
set_option cbv.warning false
namespace Verified
open Wasm
-- This is a byte parser, not a translation of the C algorithm.
def dataSegment : Option (Nat × Bytes) := do
  let (pos,len) ← sectionSpan 11
  let stop := pos+len
  let (n, pos) ← uleb pos
  if n != 1 then none else do
    let (flag, pos) ← byte pos
    let (op, pos) ← byte pos
    if flag != 0 || op != 65 then none else do
      let (addr, pos) ← sleb pos
      let (endOp, pos) ← byte pos
      if endOp != 11 then none else do
        let (size, pos) ← uleb pos
        let data ← spanBytes pos size
        if pos+size == stop then some (addr, data) else none

def expectedData : Bytes := [0,0,0,0,1,0,0,0,2,0,0,0,1,0,0,0,0,0,0,0,4,0,0,0,4,0,0,0,4,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,255,255,255,255,252,255,255,255,1,0,0,0,2,0,0,0,3,0,0,0]

theorem module_memory : getSection 5 = some [1,1,32,32] := by rfl
theorem module_functions : getSection 3 = some [6,0,1,1,2,2,2] := by rfl
theorem module_types : getSection 1 = some
  [3,96,6,127,127,127,127,127,127,1,127,96,4,127,127,127,127,1,127,96,3,127,127,127,1,127] := by rfl
theorem module_exports : getSection 7 = some
  [3,6,109,101,109,111,114,121,2,0,20,76,90,52,95,99,111,109,112,114,101,115,115,95,100,101,102,97,117,108,116,0,1,
   19,76,90,52,95,100,101,99,111,109,112,114,101,115,115,95,115,97,102,101,0,2] := by rfl
theorem module_data : dataSegment = some (65536, expectedData) := by rfl

def byteAt (bs : Bytes) (a : Nat) : Nat := bs[a]?.getD 0
def initialMemory (input : Bytes) (src dst cap : Nat) : Memory := fun a =>
  if src ≤ a && a < src + input.length then byteAt input (a-src)
  else if dst ≤ a && a < dst+cap then 165
  else if 65536 ≤ a && a < 65600 then byteAt expectedData (a-65536)
  else 0

def outcome (r : Result) : Option Nat := match r with
  | .returned v _ => some v
  | _ => none

def accesses (r : Result) : List Access := match r with
  | .returned _ s | .running s => s.accesses.reverse
  | .trap => []

def unchanged (m : Memory) (r : Result) : Prop := match r with
  | .returned _ s => s.mem = m
  | _ => False

-- Proofs below use symbolic memory: no assumptions about its contents.
theorem zero_source_zero_capacity (m : Memory) :
    outcome (execute 40 131072 262144 0 0 m) = some 4294967295 ∧
    accesses (execute 40 131072 262144 0 0 m) = [] ∧
    unchanged m (execute 40 131072 262144 0 0 m) := by
  exact ⟨rfl, rfl, rfl⟩

theorem empty_block_zero_capacity (m : Memory) :
    outcome (execute 40 131072 262144 1 0 m) =
      some (if m 131072 % 256 = 0 then 0 else 4294967295) ∧
    accesses (execute 40 131072 262144 1 0 m) = [⟨false,131072,1⟩] ∧
    unchanged m (execute 40 131072 262144 1 0 m) := by
  change (some (if m 131072 % 256 + 256 * 0 == 0 then 0 else 4294967295) = _) ∧ _ ∧ _
  simp only [Nat.mul_zero, Nat.add_zero, beq_iff_eq]
  exact ⟨True.intro, rfl, rfl⟩

-- Every byte in every machine access is checked, including reads from dst.
def inRange (p base len : Nat) : Bool := base ≤ p && p < base+len
def allowed (src size dst cap : Nat) (a : Access) : Bool :=
  (List.range a.width).all fun k =>
    let p := a.addr+k
    p < 131072 || (if a.write then inRange p dst cap
      else inRange p src size || inRange p dst cap)

structure Case where
  input : Bytes
  output : Bytes
  cap : Nat
  result : Nat
  fuel : Nat
  src : Nat := 131072
  dst : Nat := 262144

def checkCase (c : Case) : Bool :=
  match execute c.fuel c.src c.dst c.input.length c.cap
      (initialMemory c.input c.src c.dst c.cap) with
  | .returned r s => r == c.result &&
      (List.range c.output.length).all (fun k => s.mem (c.dst+k) == byteAt c.output k) &&
      s.accesses.all (allowed c.src c.input.length c.dst c.cap)
  | _ => false

def cases : List Case := [
  ⟨[], [], 1, 4294967295, 40, 131072, 262144⟩,
  ⟨[0], [], 0, 0, 40, 131072, 262144⟩,
  ⟨[0], [], 1, 0, 200, 131072, 262144⟩,
  ⟨[16,65], [65], 1, 1, 400, 131072, 262144⟩,
  ⟨[80,65,66,67,68,69], [65,66,67,68,69], 5, 5, 700, 131072, 262144⟩,
  ⟨[240,0] ++ List.replicate 15 65, List.replicate 15 65, 15, 15, 1500, 131072, 262144⟩,
  ⟨[19,65,1,0,80,66,67,68,69,70], List.replicate 8 65 ++ [66,67,68,69,70], 13, 13, 3000, 131072, 262144⟩,
  ⟨[15,0,0,1,80,66,67,68,69,70], List.replicate 20 0 ++ [66,67,68,69,70], 25, 25, 4000, 131072, 262144⟩,
  ⟨[19,65,2,0,80,66,67,68,69,70], [], 13, 4294967291, 2000, 131072, 262144⟩]

theorem concrete_cases : cases.all checkCase = true := by cbv
end Verified
