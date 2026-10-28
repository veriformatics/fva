import Proofs.Artifact
import Proofs.Format

namespace Verification

def initial (src dst size cap : Nat) (m : Memory) : State :=
  ⟨[], [src, dst, size, cap] ++ List.replicate 15 0, m, []⟩

def execute (fuel src dst size cap : Nat) (m : Memory) : Result :=
  eval shipped fuel func2.body (initial src dst size cap m)

def effect : Result → Option (Nat × Memory × List Access)
  | .normal s | .returned s => match s.stack with
    | [r] => some (r, s.mem, s.trace)
    | _ => none
  | _ => none

/- General (symbolic-memory) results about the actual extracted entry path. -/
set_option maxRecDepth 10000 in
theorem zeroCapacity (src dst size : Nat) (m : Memory)
    (hs : src ≠ 0) (hb : src + 1 ≤ memorySize) :
    effect (execute 64 src dst size 0 m) =
      some (if size = 1 then (if m src % 256 = 0 then 0 else 4294967295)
            else 4294967295, m,
        if size = 1 then [⟨false, src, 1⟩] else []) := by
  by_cases hz : size = 1
  · subst size
    simp [effect, execute, initial, func2, eval, setLocal, binary, bit,
      signed, word, modulus, readLE, hs, hb]
  · simp [effect, execute, initial, func2, eval, setLocal, binary, bit,
      signed, word, modulus, hs, hz]

set_option maxRecDepth 10000 in
theorem emptySource (src dst cap : Nat) (m : Memory)
    (hs : src ≠ 0) (hc : cap < 2147483648) :
    effect (execute 64 src dst 0 cap m) = some (4294967295, m, []) := by
  by_cases hz : cap = 0
  · subst cap
    simp [effect, execute, initial, func2, eval, setLocal, binary, bit,
      signed, word, modulus, hs]
  · simp [effect, execute, initial, func2, eval, setLocal, binary, bit,
      word, modulus, hs, hz]

def inBuffer (a base size : Nat) : Bool := base ≤ a && a < base + size

def allowed (src dst size cap : Nat) (a : Access) : Bool :=
  (List.range a.width).all fun i =>
    let p := a.addr + i
    p < 131072 || inBuffer p dst cap || (!a.write && inBuffer p src size)

def testMemory (src : Nat) (input : List Nat) : Memory := fun a =>
  if src ≤ a ∧ a < src + input.length then input[a - src]!
  else if 65536 ≤ a ∧ a < 65536 + tableBytes.length then tableBytes[a - 65536]!
  else if a ≥ 131072 then 165 else 0

structure Case where
  name : String
  src : Nat
  dst : Nat
  input : List Nat
  cap : Nat
  expected : Option (List Nat) -- none means a negative return is required
  valid : Bool               -- assert strict format/end conditions for R2
  deriving Repr

def buffersOK (c : Case) : Bool :=
  131072 ≤ c.src && c.src + c.input.length ≤ memorySize &&
  131072 ≤ c.dst && c.dst + c.cap ≤ memorySize &&
  (c.src + c.input.length ≤ c.dst || c.dst + c.cap ≤ c.src)

def checkCase (c : Case) : Bool :=
  buffersOK c && match effect (execute 5000 c.src c.dst c.input.length c.cap (testMemory c.src c.input)) with
  | none => false
  | some (r, m, trace) =>
    trace.all (allowed c.src c.dst c.input.length c.cap) &&
    match c.expected with
    | none => r ≥ 2147483648
    | some bytes =>
      r = bytes.length && r ≤ c.cap &&
      (List.range r).map (fun i => m (c.dst + i)) == bytes &&
      (match parseBlock true c.input with
       | some d => d.bytes == bytes
       | none => false) &&
      (!c.valid || (validIndependent c.input && (c.cap ≥ 1 || c.input == [0])))

end Verification
