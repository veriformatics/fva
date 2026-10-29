import Proofs.Lifted
import FVA.Spec.CAbi

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- The binary64 value immediately below 0.5. -/
def badInput : BitVec 64 := 0x3fdfffffffffffff

/-- The exact real value represented by the counterexample input bits. -/
noncomputable def badValue : ℝ := (ofBits f64fmt badInput).toReal f64fmt

/-- R1 fails: a finite in-range input with uniquely nearest integer 0 always returns 1.
The exact input is 9007199254740991 / 18014398509481984, strictly below 1/2;
the strict distance comparison excludes every nonzero integer, including 1. -/
def r1_counterexample : Prop :=
  (ofBits f64fmt badInput).IsNum ∧
  badValue = (9007199254740991 : ℝ) / 18014398509481984 ∧
  (0 ≤ badValue ∧ badValue ≤ 2147483647) ∧
  (∀ n : ℤ, n ≠ 0 → |badValue| < |badValue - (n : ℝ)|) ∧
  Returns Lifted.module "iround" [.f64 badInput] [.i32 1]

end Proofs
