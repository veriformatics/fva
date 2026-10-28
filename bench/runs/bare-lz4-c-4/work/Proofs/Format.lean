import Proofs.Wasm

/- A constructive description of the independent block grammar. The model
   encodes sequences, rather than parsing the artifact's outputs. The final
   token here has low nibble zero; other final low nibbles are not modeled. -/
namespace Verification

structure MatchSequence where
  literals : List Nat
  offset : Nat
  length : Nat

def extensionBytes (extra : Nat) : List Nat :=
  List.replicate (extra / 255) 255 ++ [extra % 255]

def encodeLiterals (literals : List Nat) : List Nat :=
  (if literals.length ≥ 15 then extensionBytes (literals.length - 15) else []) ++ literals

def encodeMatch (s : MatchSequence) : List Nat :=
  [16 * min 15 s.literals.length + min 15 (s.length - 4)] ++
    encodeLiterals s.literals ++ [s.offset % 256, s.offset / 256] ++
    (if s.length ≥ 19 then extensionBytes (s.length - 19) else [])

def encodeBlock (sequences : List MatchSequence) (tail : List Nat) : List Nat :=
  sequences.flatMap encodeMatch ++ [16 * min 15 tail.length] ++ encodeLiterals tail

def matchCopy (offset : Nat) : Nat → List Nat → List Nat
  | 0, out => out
  | n + 1, out =>
    let byte := if offset = 0 then 0 else out[out.length - offset]!
    matchCopy offset n (out ++ [byte])

def decodeSequences (allowZero : Bool) : List MatchSequence → List Nat → Option (List Nat)
  | [], out => some out
  | s :: ss, out =>
    let out := out ++ s.literals
    if s.literals.all (· < 256) && s.length ≥ 4 && s.offset ≤ 65535 &&
        s.offset ≤ out.length && (allowZero || s.offset > 0) then
      decodeSequences allowZero ss (matchCopy s.offset s.length out)
    else none

def decodedBlock (allowZero : Bool) (sequences : List MatchSequence)
    (tail : List Nat) : Option (List Nat) := do
  if !tail.all (· < 256) then none else do
    let out ← decodeSequences allowZero sequences []
    some (out ++ tail)

def matchStarts : List MatchSequence → Nat → List Nat
  | [], _ => []
  | s :: ss, n =>
    (n + s.literals.length) :: matchStarts ss (n + s.literals.length + s.length)

def validIndependentBlock (sequences : List MatchSequence) (tail : List Nat) : Bool :=
  match decodedBlock false sequences tail with
  | none => false
  | some out =>
    (sequences.isEmpty || tail.length ≥ 5) &&
    (matchStarts sequences 0).all (fun start => start + 12 ≤ out.length)

def overlapSequences : List MatchSequence := [⟨[65], 1, 7⟩]
def zeroSequences : List MatchSequence := [⟨[65], 0, 7⟩]
def exampleTail : List Nat := [66, 67, 68, 69, 70]

theorem overlapFormat :
    validIndependentBlock overlapSequences exampleTail = true ∧
    encodeBlock overlapSequences exampleTail = [19, 65, 1, 0, 80, 66, 67, 68, 69, 70] ∧
    decodedBlock false overlapSequences exampleTail =
      some [65, 65, 65, 65, 65, 65, 65, 65, 66, 67, 68, 69, 70] := by decide

theorem zeroOffsetFormat :
    encodeBlock zeroSequences exampleTail = [19, 65, 0, 0, 80, 66, 67, 68, 69, 70] ∧
    decodedBlock true zeroSequences exampleTail =
      some [65, 0, 0, 0, 0, 0, 0, 0, 66, 67, 68, 69, 70] ∧
    validIndependentBlock zeroSequences exampleTail = false := by decide

theorem emptyFormat :
    validIndependentBlock [] [] = true ∧ encodeBlock [] [] = [0] ∧
    decodedBlock false [] [] = some [] := by decide

theorem literalFormat :
    validIndependentBlock [] [65, 66, 67] = true ∧
    encodeBlock [] [65, 66, 67] = [48, 65, 66, 67] ∧
    decodedBlock false [] [65, 66, 67] = some [65, 66, 67] := by decide

theorem extensionFormat :
    validIndependentBlock [] (List.replicate 15 42) = true ∧
    encodeBlock [] (List.replicate 15 42) = [240, 0] ++ List.replicate 15 42 ∧
    decodedBlock false [] (List.replicate 15 42) = some (List.replicate 15 42) := by decide

end Verification
