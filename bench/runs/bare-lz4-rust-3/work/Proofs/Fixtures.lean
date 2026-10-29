import Proofs.Properties
namespace Verification
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Case where
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  src : Nat := 131072
  dst : Nat := 1048576
  deriving Inhabited, Repr

def initialMemory (c : Case) (addr : Nat) : Nat :=
  if c.src ≤ addr && addr < c.src+c.input.length then c.input[addr-c.src]!
  else if c.dst ≤ addr && addr < c.dst+c.cap then 170 else 0

def within (addr size base len : Nat) : Bool := base ≤ addr && addr+size ≤ base+len

def accessOK (c : Case) (a : Access) : Bool :=
  -- Addresses below the caller region are exempt in R1.
  (List.range a.size).all fun i =>
    let b := a.addr+i
    b < 131072 ||
      (within b 1 c.dst c.cap || (!a.write && within b 1 c.src c.input.length))

def admissible (c : Case) : Bool :=
  within c.src c.input.length 131072 (2097152-131072) &&
  within c.dst c.cap 131072 (2097152-131072) &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src)

def caseState (c : Case) : State :=
  run decoder (initialMemory c) (if c.cap > 300 then 13000 else 2000) (start c.src c.dst c.input.length c.cap)

def checkCase (c : Case) : Bool :=
  let s := caseState c
  admissible c && !s.failed && s.accesses.all (fun a => 131072 ≤ a.addr) &&
  s.accesses.all (accessOK c) &&
  match c.expected with
  | none => s.result == some 4294967295
  | some out => s.result == some out.length && out.length ≤ c.cap &&
      (List.range out.length).all (fun i => byteAt (initialMemory c) s (c.dst+i) == out[i]!)

-- Independent executable reading of the format, without Wasm optimizations.
def extraLength : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _+1, [] => none
  | fuel+1, b::bs => if b == 255 then do
      let (n, rest) ← extraLength fuel bs
      pure (b+n, rest)
    else some (b, bs)

def lengthField (field : Nat) (rest : List Nat) : Option (Nat × List Nat) :=
  if field == 15 then do
    let (n, tail) ← extraLength (rest.length+1) rest
    pure (15+n, tail)
  else some (field, rest)

def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n+1, out => matchCopy offset n (out ++ [out[out.length-offset]!])

structure Parsed where
  output : List Nat
  matchStarts : List Nat
  finalLiterals : Nat
  deriving BEq, Repr

def parseSeq : Nat → List Nat → List Nat → List Nat → Option Parsed
  | 0, _, _, _ => none
  | _+1, [], out, starts => some ⟨out, starts, 0⟩
  | fuel+1, token::rest, out, starts => do
      let (n, rest) ← lengthField (token/16) rest
      if n > rest.length then none else do
        let out := out ++ rest.take n
        let rest := rest.drop n
        if rest.isEmpty then some ⟨out, starts, n⟩ else
          match rest with
          | lo::hi::tail => do
            let offset := lo+256*hi
            if offset == 0 || offset > out.length then none else do
              let (m, tail) ← lengthField (token%16) tail
              parseSeq fuel tail (matchCopy offset (m+4) out) (starts ++ [out.length])
          | _ => none

def parse (bytes : List Nat) : Option Parsed :=
  if bytes.isEmpty then none else parseSeq (bytes.length+1) bytes [] []

def validEnd (p : Parsed) : Bool :=
  match p.matchStarts.getLast? with
  | none => p.output.length < 5 || p.finalLiterals ≥ 5
  | some pos => p.finalLiterals ≥ 5 && p.output.length-pos ≥ 12

-- Test data builders are separate from both the Wasm model and format parser.
def extBytes (n : Nat) : List Nat := List.replicate (n/255) 255 ++ [n%255]
def literalBlock (xs : List Nat) : List Nat :=
  if xs.length < 15 then [xs.length*16] ++ xs
  else [240] ++ extBytes (xs.length-15) ++ xs

def patterned (n : Nat) : List Nat := (List.range n).map (fun i => (i*37+11)%256)

def literalCases : List Case :=
  ([0,1,2,3,4,5,7,8,14,15,16,17,31,32,33,64,65,128,269,270,300] : List Nat).map
    (fun n => ⟨literalBlock (patterned n), n, some (patterned n), 131072, 1048576⟩)

-- Match sizes 4, 7, 18, 19, 32, 33, 64, 65 and 300; varied offsets,
-- optional length bytes, and enough final literals for the format end conditions.
def matchedCase (lits offset m tailLen capExtra : Nat) : Case := Id.run do
  let head := patterned lits
  let tail := patterned tailLen
  let token := (min lits 15)*16 + min (m-4) 15
  let input := [token] ++ (if lits < 15 then [] else extBytes (lits-15)) ++ head ++
    [offset%256, offset/256] ++ (if m < 19 then [] else extBytes (m-19)) ++ literalBlock tail
  let out := matchCopy offset m head ++ tail
  return ⟨input, out.length+capExtra, some out, 131072, 1048576⟩

def matchCases : List Case := [
  matchedCase 1 1 7 5 0,
  matchedCase 2 2 7 5 64,
  matchedCase 8 8 4 8 0,
  matchedCase 14 14 18 5 64,
  matchedCase 16 16 19 5 0,
  matchedCase 32 32 32 5 64,
  matchedCase 33 33 33 5 64,
  matchedCase 64 64 64 5 64,
  matchedCase 65 65 65 5 0,
  matchedCase 1 1 300 5 0,
  matchedCase 3 3 300 5 0,
  -- Short-token hot path (input >= 19, cap > 34); overlapping/nonoverlapping.
  matchedCase 1 1 7 32 64,
  matchedCase 8 8 7 32 64,
  matchedCase 14 14 4 32 64]

def invalidCases : List Case :=
  ([[], [240], [240,255], [32,65], [16,65,0], [16,65,0,0],
    [16,65,2,0], [31,65,1,0], [31,65,1,0,255],
    [0,1,0], [0,0,0], [32,65,66,3,0]] : List (List Nat)).map
    (fun xs => ⟨xs, 128, none, 131072, 1048576⟩)

def shortCapacityCases : List Case :=
  [⟨[16,65], 0, none, 131072, 1048576⟩,
   ⟨[16,65,1,0,80,66,67,68,69,70], 4, none, 131072, 1048576⟩,
   ⟨literalBlock (patterned 32), 31, none, 131072, 1048576⟩]

-- End-condition probes: a match-only ending is rejected; a trailing empty sequence is accepted.
def relaxedCases : List Case :=
  [⟨[16,65,1,0], 5, none, 131072, 1048576⟩,
   ⟨[16,65,1,0,0], 5, some [65,65,65,65,65], 131072, 1048576⟩,
   ⟨[15], 0, some [], 131072, 1048576⟩]

def validCases : List Case := literalCases ++ matchCases

def edgeCases : List Case :=
  [⟨[16,65], 1, some [65], 2097150, 131072⟩,
   ⟨[16,65], 1, some [65], 131072, 2097151⟩,
   ⟨[16,65], 1, some [65], 131072, 131074⟩,
   ⟨[16,65], 1, some [65], 131073, 131072⟩,
   ⟨[0], 0, some [], 2097151, 131072⟩]

def corpus : List Case := validCases ++ invalidCases ++ shortCapacityCases ++ relaxedCases ++ edgeCases

def referenceAgrees (c : Case) : Bool :=
  match c.expected with
  | none => true -- Capacity errors are checked against the actual model, not inferred here.
  | some out => match parse c.input with
    | none => false
    | some p => p.output == out

def validReference (c : Case) : Bool :=
  match parse c.input, c.expected with
  | some p, some out => validEnd p && p.output == out && out.length ≤ c.cap
  | _, _ => false

-- All tokens, with no output capacity and with ample output capacity.
def tokenCases : List Case := (List.range 256).flatMap fun token =>
  [0,64].map fun cap => ⟨[token], cap, if token < 16 then some [] else none, 131072, 1048576⟩

-- Small kernel certificate set; the full corpus is also checked by executable assertions.
def certifiedCases : List Case := [
  ⟨[0], 0, some [], 131072, 1048576⟩,
  ⟨[16,11], 1, some [11], 131072, 1048576⟩,
  ⟨[19,11,1,0,80,11,48,85,122,159], 13,
    some [11,11,11,11,11,11,11,11,11,48,85,122,159], 131072, 1048576⟩,
  ⟨[16,65,0,0], 128, none, 131072, 1048576⟩,
  ⟨[16,65,1,0,0], 5, some [65,65,65,65,65], 131072, 1048576⟩]

def certifiedValidCases : List Case := certifiedCases.take 3

def certifiedTokens : List Case := ([0,15,16,240] : List Nat).map fun token =>
  ⟨[token], 0, if token < 16 then some [] else none, 131072, 1048576⟩

end Verification
