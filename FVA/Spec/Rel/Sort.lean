import FVA.Spec.Rel.Text

/-! # Sorted integers (reviewed once; contract U9 B2) -/

namespace FVA.Cert

/-- Integers as text: each in decimal, a `-` (byte 45) before a negative one, followed by a line
feed (byte 10). -/
def IntLines (xs : List Int) : List UInt8 :=
  xs.flatMap fun x => (if x < 0 then [45] else []) ++ decimal x.natAbs ++ [10]

/-- The output lists the input's integers in nondecreasing order, one per line: both files are
`IntLines`, the output's integers are the input's (each as often), and each is at most the next.
-/
def SortedPerm (i o : List UInt8) : Prop :=
  ∃ xs ys, i = IntLines xs ∧ o = IntLines ys ∧ ys.Pairwise (· ≤ ·) ∧ ys.Perm xs

end FVA.Cert
