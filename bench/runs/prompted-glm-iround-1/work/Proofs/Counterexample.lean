import Init
namespace Verification

def Nearest (num den result : Int) : Prop :=
  ∀ n : Int, (num - result * den).natAbs ≤ (num - n * den).natAbs

theorem r1_counterexample :
    let num : Int := 9007199254740991
    let den : Int := 18014398509481984
    0 < den ∧ 0 ≤ num ∧ num ≤ 2147483647 * den ∧
      (num - 0 * den).natAbs < (num - 1 * den).natAbs ∧ ¬ Nearest num den 1 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  have wrong : ¬ (9007199254740991 - 1 * 18014398509481984 : Int).natAbs ≤
      (9007199254740991 - 0 * 18014398509481984 : Int).natAbs := by decide +kernel
  intro h
  exact wrong (h 0)
end Verification
#print axioms Verification.r1_counterexample
