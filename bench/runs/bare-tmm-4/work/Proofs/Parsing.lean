import Mathlib.Tactic

namespace Verification
/-- A structurally recursive splitter, suitable for kernel reduction. -/
def splitChars (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let rest := splitChars sep cs
    if c = sep then [] :: rest else
      match rest with
      | [] => [[c]]
      | a :: more => (c :: a) :: more

/-- Nonempty unsigned decimal digits. Invalid characters are rejected. -/
def digits (cs : List Char) : Option ℕ := do
  if cs.isEmpty then none else
    cs.foldlM (fun n c =>
      if '0' ≤ c ∧ c ≤ '9' then some (10*n + c.toNat - '0'.toNat) else none) 0

def parseDecimal (cs : List Char) : Option ℚ := do
  let [a,b] := splitChars '.' cs | none
  let x ← digits a
  let y ← digits b
  return (x : ℚ) + (y : ℚ) / 10 ^ b.length

/-- One positive decimal per line, including a required final LF. -/
def parseFactors (s : String) : Option (List ℚ) := do
  let parts := splitChars '\n' s.toList
  if parts.getLast? != some [] then none else
    parts.dropLast.mapM parseDecimal
end Verification

namespace Verification
/-- Nonnegative integer matrix, with tabs separating columns and a final LF. -/
def parseCounts (s : String) : Option (List (List ℕ)) := do
  let parts := splitChars '\n' s.toList
  if parts.getLast? != some [] then none else
    parts.dropLast.mapM (fun line => (splitChars '\t' line).mapM digits)
end Verification
