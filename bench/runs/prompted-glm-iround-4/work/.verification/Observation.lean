import Proofs.Counterexample
theorem observation_link :
    (4602678819172646911 : Nat) = 1021 * 2^52 + (2^52 - 1) ∧
    (0 : Nat) < 1021 ∧ (1021 : Nat) < 2047 ∧
    Counterexample.numerator = Int.ofNat (2^52 + (2^52 - 1)) ∧
    Counterexample.denominator = Int.ofNat (2^(1075 - 1021)) ∧
    Counterexample.output = 1 := by decide +kernel
