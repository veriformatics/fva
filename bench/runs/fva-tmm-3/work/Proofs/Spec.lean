import Proofs.Model
import Proofs.Counts
import Proofs.Edge
import Proofs.RNA

namespace Proofs

/-- R1 counterexample at tolerance 1e-10: on the exact shipped 454-by-7 matrix,
sample 3 differs from the documented exact-real TMM by more than 0.01.
This uses exact average ranks, not R's floating point splitting of ties. -/
def R1_failure : Prop :=
  ∃ (xs : Matrix) (ds : List Decimal),
    Counts.blob.data = countBytes xs ∧ Edge.blob.data = factorBytes ds ∧
    xs.length = 454 ∧ (∀ row ∈ xs, row.length = 7) ∧ ds.length = 7 ∧
    reference xs = 3 ∧
    (decimalValue (ds[2]?.getD (0,0)) : ℝ) + 1/100 < factor xs 2

/-- R2 counterexample at tolerance 1e-10: sample 3 in the exact shipped RNAnorm
output differs from the documented exact-real TMM by more than 0.01.
The two documented mathematical procedures agree under exact average ranks. -/
def R2_failure : Prop :=
  ∃ (xs : Matrix) (ds : List Decimal),
    Counts.blob.data = countBytes xs ∧ RNA.blob.data = factorBytes ds ∧
    xs.length = 454 ∧ (∀ row ∈ xs, row.length = 7) ∧ ds.length = 7 ∧
    reference xs = 3 ∧
    (decimalValue (ds[2]?.getD (0,0)) : ℝ) + 1/100 < factor xs 2

/-- R3 fails directly on the output bytes: all seven corresponding decimals
differ by more than 1e-10; sample 1 differs by more than 0.009. -/
def R3_failure : Prop :=
  ∃ es rs : List Decimal,
    Edge.blob.data = factorBytes es ∧ RNA.blob.data = factorBytes rs ∧
    es.length = 7 ∧ rs.length = 7 ∧
    (∀ i ∈ List.range 7,
      1/10000000000 < |decimalValue (es[i]?.getD (0,0)) -
        decimalValue (rs[i]?.getD (0,0))|) ∧
    9/1000 < |decimalValue (es[0]?.getD (0,0)) - decimalValue (rs[0]?.getD (0,0))|

end Proofs
