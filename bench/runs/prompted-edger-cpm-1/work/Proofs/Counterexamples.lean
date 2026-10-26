/- Arithmetic certificates for the executed counterexamples. No execution model.
   All divisions here are exact integer divisions; float observations are checked
   separately by verify/check.py and verify/filter.R. -/
import Init

set_option maxRecDepth 10000
set_option exponentiation.threshold 2048

namespace Evidence

-- c = L = 2^1023 are finite binary64 values. Correct CPM is exactly 1000000;
-- the implementation's intermediate product exceeds even 2^1024.
theorem r1_witness :
    0 < (2^1023 : Nat) ∧
    2^1023 ≤ (2^53-1)*2^971 ∧
    (2^1023*1000000)/2^1023 = 1000000 ∧
    2^1024 ≤ 2^1023*1000000 ∧
    1000000 < 2^53 := by decide

-- First gene: 20 counts, min.count 20, total >= 15, one required sample.
-- True CPM is 5000000/9. Observed CPM and cutoff have the common denominator
-- 2^33 = 8589934592 and the numerators below; they straddle the true value.
theorem r2_boundary_witness :
    (20 : Nat) ≥ 20 ∧ 20 ≥ 15 ∧ (1 : Nat) ≥ 1 ∧
    20*1000000*9 = 5000000*36 ∧
    4772185884444444*9 < 5000000*8589934592 ∧
    5000000*8589934592 < 4772185884444445*9 ∧
    (4772185884444444 : Nat) < 4772185884444445 := by decide

-- One qualifying sample is strictly less than 1+2^-50. The excess is smaller
-- than the exact binary64 value of 1e-14, namely 6338253001141147/2^99.
theorem r2_tolerance_witness :
    (1 : Nat)*2^50 < 2^50+1 ∧
    (2^99 : Nat) < 6338253001141147*2^50 ∧
    (20 : Nat) ≥ 10 ∧ 0 < (10 : Nat) ∧ 20 ≥ 15 := by decide

end Evidence

#print axioms Evidence.r1_witness
#print axioms Evidence.r2_boundary_witness
#print axioms Evidence.r2_tolerance_witness
