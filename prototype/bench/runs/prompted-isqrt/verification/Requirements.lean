import Correctness

open Wasm

-- R2: a finite byte-level execution returns. R1: every returned result is
-- the largest natural number whose non-wrapping square is at most n.
theorem requirements (n : Nat) (hn : n < 2^32) :
    (∃ r, invoke Artifact.bytes n r) ∧
    (∀ r, invoke Artifact.bytes n r → r < 65536 ∧ IsSqrt n r) := by
  obtain ⟨answer,hr,hs⟩ := Verification.invocation_exists n hn
  refine ⟨⟨answer,hr⟩, ?_⟩
  intro r he
  have eqr := Verification.results_unique hr.2.2.2 he.2.2.2
  subst r
  refine ⟨?_, hs⟩
  by_cases h : answer < 65536
  · exact h
  have hm := Nat.mul_self_le_mul_self (show 65536 ≤ answer by omega)
  have hl := hs.1
  omega

#print axioms requirements
