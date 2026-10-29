import Proofs.Artifact

namespace Verification

/-- Declarative format evaluator: length fields, literals, and bytewise backward matches. -/
def lengthField (base : Nat) : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | fuel+1, bs =>
    if base < 15 then some (base, bs) else
      match bs with
      | [] => none
      | b :: rest => if b < 255 then some (15+b,rest) else do
        let (n,tail) ← lengthField 15 fuel rest
        pure (255+n,tail)

def matchBytes : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, out => some out
  | fuel+1, offset, out => do
    if offset == 0 || offset > out.length then none else
      let b ← out[out.length-offset]?
      matchBytes fuel offset (out ++ [b])

structure Parsed where
  out : List Nat
  finalLiterals : Nat
  lastMatch : Option Nat
  deriving DecidableEq, Repr

def sequences : Nat → List Nat → List Nat → Option Nat → Option Parsed
  | 0, _, _, _ => none
  | fuel+1, input, out, lastMatch => do
    let token :: rest := input | none
    let (n,rest) ← lengthField (token/16) (fuel+1) rest
    if n > rest.length then none else
      let out := out ++ rest.take n
      let rest := rest.drop n
      if rest.isEmpty then some ⟨out,n,lastMatch⟩ else do
        let lo :: hi :: rest := rest | none
        let offset := lo + 256*hi
        let (n,rest) ← lengthField (token%16) (fuel+1) rest
        let next ← matchBytes (n+4) offset out
        sequences fuel rest next (some out.length)

def parse (input : List Nat) : Option Parsed := sequences (input.length+1) input [] none

def endConditions (p : Parsed) : Bool :=
  match p.lastMatch with
  | none => true
  | some start => p.finalLiterals ≥ 5 && start+12 ≤ p.out.length

structure Case where
  input : List Nat
  cap : Nat
  expected : Option (List Nat)
  src : Nat := 131072
  dst : Nat := 262144
  deriving DecidableEq, Repr

def inBuffer (a size base len : Nat) : Bool := base ≤ a && a+size ≤ base+len

def admissible (c : Case) : Bool :=
  c.input.all (· < 256) &&
  131072 ≤ c.src && c.src+c.input.length ≤ 2097152 &&
  131072 ≤ c.dst && c.dst+c.cap ≤ 2097152 &&
  (c.src+c.input.length ≤ c.dst || c.dst+c.cap ≤ c.src)

def permitted (c : Case) (access : Access) : Bool :=
  -- Accesses below 131072 are unrestricted by R1; straddling accesses are checked bytewise.
  (List.range access.size).all fun i =>
    let a := access.addr+i
    a < 131072 || inBuffer a 1 c.dst c.cap ||
      (!access.write && inBuffer a 1 c.src c.input.length)

def memory (c : Case) : Memory :=
  putBytes (putBytes Artifact.initialData c.dst (List.replicate c.cap 204)) c.src c.input

def execution (c : Case) : Option State :=
  run Artifact.code Artifact.ends 2500 (initial c.src c.dst c.input.length c.cap (memory c))

/-- Concrete R1 plus expected return/output. On success also checks R3's parse/content/cap.
    On failure independently checks that there was no valid fitting block (R2 antecedent).
    Successful corpus entries must meet the end conditions (so exercise R2 as well). -/
def checkCase (c : Case) : Bool :=
  admissible c && match execution c with
  | none => false
  | some s => s.accesses.all (permitted c) && match c.expected with
    | none => s.result == some (2^32-1) &&
        match parse c.input with
        | none => true
        | some p => !endConditions p || p.out.length > c.cap
    | some expected => s.result == some expected.length && expected.length ≤ c.cap &&
        (List.range expected.length).map (fun i => readByte s.mem (c.dst+i)) == expected &&
        match parse c.input with
        | none => false
        | some p => p.out == expected && endConditions p

-- These are finite proof instances, not universal quantification over the README domain.
def cases : List Case := [
  ⟨[],64,none,131072,262144⟩,
  ⟨[0],0,some [],131072,262144⟩,
  ⟨[80,104,101,108,108,111],5,some [104,101,108,108,111],131072,262144⟩,
  ⟨[240,0] ++ List.range 15,15,some (List.range 15),131072,262144⟩,
  ⟨[80,104,101,108,108,111],4,none,131072,262144⟩,
  ⟨[16,65,0,0,80,66,67,68,69,70],64,none,131072,262144⟩,
  ⟨[0,1,0,80,66,67,68,69,70],64,none,131072,262144⟩,
  ⟨[240],64,none,131072,262144⟩,
  ⟨[16,65,1],64,none,131072,262144⟩,
  ⟨[19,65,1,0,80,66,67,68,69,70],13,
    some (List.replicate 8 65 ++ [66,67,68,69,70]),131072,262144⟩,
  ⟨[20,65,1,0,240,0] ++ List.range 15,64,
    some (List.replicate 9 65 ++ List.range 15),131072,262144⟩,
  ⟨[128] ++ List.range 8 ++ [8,0,240,0] ++ List.range 15,64,
    some (List.range 8 ++ List.range 4 ++ List.range 15),131072,262144⟩,
  ⟨[31,65,1,0,1,80,66,67,68,69,70],26,
    some (List.replicate 21 65 ++ [66,67,68,69,70]),131072,262144⟩,
  ⟨[80,104,101,108,108,111],5,some [104,101,108,108,111],2097146,131072⟩,
  ⟨[80,104,101,108,108,111],5,some [104,101,108,108,111],131072,2097147⟩
]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem empty_input (src dst cap : Nat) (mem : Memory) :
    observe (run Artifact.code Artifact.ends 10 (initial src dst 0 cap mem)) =
      some (2^32-1, mem, []) := by rfl

theorem corpus : cases.all checkCase = true := by decide +kernel

#print axioms Artifact.lift_exact
#print axioms Artifact.ends_exact
#print axioms empty_input
#print axioms corpus
end Verification
