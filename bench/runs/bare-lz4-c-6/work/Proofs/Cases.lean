import Proofs.Artifact
import Proofs.Format

namespace Cases
open Wasm Artifact LZ4Spec

structure Case where
  name : String
  input : List Nat
  capacity : Nat
  expected : Int
  src : Nat := 131072
  dst : Nat := 262144
  deriving Repr, Inhabited

def memory (c : Case) : Memory :=
  ⟨fun a => if c.src ≤ a && a < c.src + c.input.length then c.input[a - c.src]!
    else if a ≥ 131072 then 165 else Artifact.initialByte a, []⟩

def conforms (c : Case) : Bool := Id.run do
  if !(131072 ≤ c.src && c.src + c.input.length ≤ 2097152 &&
      131072 ≤ c.dst && c.dst + c.capacity ≤ 2097152 &&
      (c.src + c.input.length ≤ c.dst || c.dst + c.capacity ≤ c.src)) then
    return false
  let some s := run 100000 program (initial c.src c.dst c.input.length c.capacity (memory c))
    | return false
  let some r := s.result | return false
  if signed r != c.expected then return false
  if !s.accesses.all (allowed c.src c.input.length c.dst c.capacity) then return false
  -- R2, for those samples that satisfy the independently checked premise.
  if validIndependent c.input &&
      (c.capacity ≥ 1 || c.input == [0]) then
    let some decoded := decode c.input | return false
    if decoded.bytes.length ≤ c.capacity then
      if signed r != (decoded.bytes.length : Int) then return false
  -- R3, for every successful sample, including accepted invalid end conditions.
  if signed r ≥ 0 then
    if r > c.capacity then return false
    let some decoded := decode c.input | return false
    if decoded.bytes.length != r then return false
    if !(List.range r).all (fun i => s.memory.get (c.dst + i) == decoded.bytes[i]!) then
      return false
  return true

def examples : List Case := [
  ⟨"no input/no output", [], 0, -1 , 131072, 262144⟩,
  ⟨"no input/positive output", [], 1, -1 , 131072, 262144⟩,
  ⟨"empty block/no output", [0], 0, 0 , 131072, 262144⟩,
  ⟨"empty block/positive output", [0], 1, 0 , 131072, 262144⟩,
  ⟨"nonzero empty token/no output", [1], 0, -1 , 131072, 262144⟩,
  ⟨"nonzero empty token/positive output", [15], 1, 0 , 131072, 262144⟩,
  ⟨"one literal", [16,65], 1, 1 , 131072, 262144⟩,
  ⟨"one literal/no output", [16,65], 0, -1 , 131072, 262144⟩,
  ⟨"one literal/large output", [16,65], 64, 1 , 131072, 262144⟩,
  ⟨"truncated literal", [16], 1, -2 , 131072, 262144⟩,
  ⟨"truncated literal extension", [240], 64, -2 , 131072, 262144⟩,
  ⟨"14 literals", 224 :: List.replicate 14 66, 14, 14 , 131072, 262144⟩,
  ⟨"15 literals", [240,0] ++ List.replicate 15 67, 15, 15 , 131072, 262144⟩,
  ⟨"15 literals/insufficient output", [240,0] ++ List.replicate 15 67, 14, -3 , 131072, 262144⟩,
  ⟨"offset-one overlap", [19,65,1,0,80,66,67,68,69,70], 13, 13 , 131072, 262144⟩,
  ⟨"offset-one overlap/large output", [19,65,1,0,80,66,67,68,69,70], 64, 13 , 131072, 262144⟩,
  ⟨"zero-offset match", [3,0,0,80,66,67,68,69,70], 12, 12 , 131072, 262144⟩,
  ⟨"offset beyond output", [3,1,0,80,66,67,68,69,70], 12, -4 , 131072, 262144⟩,
  ⟨"long match", [31,65,1,0,0,80,66,67,68,69,70], 25, 25 , 131072, 262144⟩,
  ⟨"offset-two overlap", [38,65,66,2,0,80,67,68,69,70,71], 17, 17 , 131072, 262144⟩,
  ⟨"offset-three overlap", [53,65,66,67,3,0,80,68,69,70,71,72], 17, 17 , 131072, 262144⟩,
  ⟨"offset-four overlap", [68,65,66,67,68,4,0,80,69,70,71,72,73], 17, 17 , 131072, 262144⟩,
  ⟨"offset-five overlap", [83,65,66,67,68,69,5,0,80,70,71,72,73,74], 17, 17 , 131072, 262144⟩,
  ⟨"offset-six overlap", [99,65,66,67,68,69,70,6,0,80,71,72,73,74,75], 18, 18 , 131072, 262144⟩,
  ⟨"offset-seven overlap", [115,65,66,67,68,69,70,71,7,0,80,72,73,74,75,76], 19, 19 , 131072, 262144⟩,
  ⟨"offset-eight copy", [131,65,66,67,68,69,70,71,72,8,0,80,73,74,75,76,77], 20, 20 , 131072, 262144⟩,
  ⟨"shortcut long literals", [131,65,66,67,68,69,70,71,72,8,0,160] ++ List.replicate 10 73, 64, 25 , 131072, 262144⟩,
  ⟨"invalid end match distance", [16,65,1,0,80,66,67,68,69,70], 10, -2 , 131072, 262144⟩,
  ⟨"short final literals rejected", [19,65,1,0,16,66], 64, -2 , 131072, 262144⟩,
  ⟨"source at top of memory", [16,65], 1, 1, 2097150, 131072⟩,
  ⟨"destination at top of memory", [16,65], 1, 1, 131072, 2097151⟩,
  ⟨"adjacent buffers", [16,65], 1, 1, 131072, 131074⟩,
  ⟨"reverse adjacent buffers", [16,65], 1, 1, 131073, 131072⟩
]

end Cases
