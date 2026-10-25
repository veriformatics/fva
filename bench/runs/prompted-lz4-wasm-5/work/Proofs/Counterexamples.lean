import Init

set_option autoImplicit false

namespace Counterexamples

-- Restricted specification fragment: two sequences, no length extensions,
-- one offset-1 match. The final token's low nibble is zero.
def wire (lits : List Nat) (matchLen : Nat) (tail : List Nat) : List Nat :=
  [16 * lits.length + (matchLen - 4)] ++ lits ++
  [1, 0, 16 * tail.length] ++ tail

def content (lits : List Nat) (matchLen : Nat) (tail : List Nat) : List Nat :=
  lits ++ List.replicate matchLen (lits.getLastD 0) ++ tail

-- The two mandatory numeric end conditions for a block containing a match.
def EndOK (matchLen : Nat) (tail : List Nat) : Prop :=
  5 ≤ tail.length ∧ 12 ≤ matchLen + tail.length

-- Sufficient validity conditions for this restricted fragment, not a full parser.
def RunValid (lits : List Nat) (matchLen : Nat) (tail : List Nat) : Prop :=
  0 < lits.length ∧ lits.length < 15 ∧ tail.length < 15 ∧
  (lits ++ tail).all (fun b => b < 256) = true ∧
  4 ≤ matchLen ∧ matchLen < 19 ∧ EndOK matchLen tail

def encoderInput : List Nat := [97,98,99,100,100,100,100,100,101,102,103,104,105]
def encoderBlock : List Nat := [64,97,98,99,100,1,0,80,101,102,103,104,105]
def decoderBlock : List Nat := [19,97,1,0,80,98,99,100,101,102]
def decoderContent : List Nat := [97,97,97,97,97,97,97,97,98,99,100,101,102]

theorem r1 :
    wire [97,98,99,100] 4 [101,102,103,104,105] = encoderBlock ∧
    content [97,98,99,100] 4 [101,102,103,104,105] = encoderInput ∧
    ¬ EndOK 4 [101,102,103,104,105] := by
  unfold EndOK
  decide

theorem r2 :
    RunValid [97] 7 [98,99,100,101,102] ∧
    wire [97] 7 [98,99,100,101,102] = decoderBlock ∧
    content [97] 7 [98,99,100,101,102] = decoderContent ∧
    decoderContent.length = 13 ∧ (1 : Nat) ≠ decoderContent.length := by
  unfold RunValid EndOK
  decide

-- The format explicitly permits [0] as the empty block. At this placement,
-- its first byte is in bounds and the following byte is outside both block
-- and memory. Executable checks establish that the decoder loads that byte.
theorem r3 : 65535 + [0].length = 65536 ∧
    ¬ (65536 < 65535 + [0].length) ∧ ¬ (65536 < 65536) := by decide

-- An export mutation replaces this proof's type with False, for kernel tests.
theorem kernelCanary : True := True.intro
theorem falseIdentity : False → False := fun h => h

end Counterexamples
