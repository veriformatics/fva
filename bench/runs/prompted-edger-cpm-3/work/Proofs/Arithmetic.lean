import Init

set_option exponentiation.threshold 2048
set_option maxRecDepth 8192

namespace Evidence

-- Exact integer facts underlying the R1 execution witness, not a Wasm model.
theorem r1_witness :
    0 < Nat.pow 2 1020 ∧
    Nat.pow 2 1020 < Nat.pow 2 1023 ∧
    Nat.mul (Nat.pow 2 1020) 1000000 = Nat.mul 1000000 (Nat.pow 2 1020) ∧
    1000000 < Nat.pow 2 53 ∧
    Nat.pow 2 1024 < Nat.mul (Nat.pow 2 1020) 1000000 := by decide

-- R2's default total-count condition is independent of its sample condition.
theorem r2_total : (10 : Nat) ≤ 10 ∧ ¬ (15 : Nat) ≤ 10 := by decide

-- Cross-multiplied exact facts for k = 1 + 2^-48 and tol = 10^-14.
-- Thus 1 < k but k - tol < 1, while the witness total 20 exceeds 15.
theorem r2_tolerance :
    Nat.pow 2 48 < Nat.add (Nat.pow 2 48) 1 ∧
    Nat.pow 10 14 < Nat.pow 2 48 ∧
    (15 : Nat) ≤ 20 := by decide

end Evidence
