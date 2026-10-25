import Init

namespace FormatFacts

-- End-of-block rule 2, including its small-input exception.
def TailOK (decodedSize finalLiterals : Nat) : Prop :=
  5 ≤ finalLiterals ∨ (decodedSize < 5 ∧ finalLiterals = decodedSize)

-- End-of-block rule 3: distance from the last match start to decoded end.
def LastMatchOK (matchLength finalLiterals : Nat) : Prop :=
  12 ≤ matchLength + finalLiterals

-- The literal-only fragment of the format (no extension byte is needed).
def LiteralBlock (block content : List Nat) : Prop :=
  content.length < 15 ∧ block = (16 * content.length) :: content

-- R1 witness: five literals, a four-byte match, four final literals.
theorem r1_bad_tail : ¬ TailOK (5 + 4 + 4) 4 := by unfold TailOK; decide

theorem r1_bad_match : ¬ LastMatchOK 4 4 := by unfold LastMatchOK; decide

-- R2 witness: one literal, offset 1, a seven-byte match, five final literals.
theorem r2_end_rules : TailOK (1 + 7 + 5) 5 ∧ LastMatchOK 7 5 := by unfold TailOK LastMatchOK; decide

-- R2/R3 witness: the specification explicitly permits [0] for empty content.
theorem empty_literal_block : LiteralBlock [0] [] := ⟨by decide, rfl⟩

theorem empty_tail : TailOK 0 0 := by unfold TailOK; decide

-- A positive control for the exported-proof mutation test.
theorem kernel_control : (0 : Nat) = 0 := rfl

end FormatFacts

#print axioms FormatFacts.r1_bad_tail
#print axioms FormatFacts.r1_bad_match
#print axioms FormatFacts.r2_end_rules
#print axioms FormatFacts.empty_literal_block
#print axioms FormatFacts.empty_tail
#print axioms FormatFacts.kernel_control
