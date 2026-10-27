import Proofs.Spec
import Proofs.Numeric
import Proofs.Discrepancy

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Proofs

theorem R1_holds : R1 := by
  refine ⟨Witness.matrix, Witness.edger, Witness.counts_eq, Witness.edger_eq,
    Witness.matrix_ok, rfl, ?_⟩
  intro j hj
  simp only [List.mem_range] at hj
  interval_cases j
  · have h := Numeric.factor0
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor1
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor2
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor3
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor4
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor5
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor6
    norm_num [Witness.edger, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
theorem R2_holds : R2 := by
  refine ⟨Witness.matrix, Witness.rnanorm, Witness.counts_eq, Witness.rnanorm_eq,
    Witness.matrix_ok, rfl, ?_⟩
  intro j hj
  simp only [List.mem_range] at hj
  interval_cases j
  · have h := Numeric.factor0
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor1
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor2
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor3
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor4
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor5
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have h := Numeric.factor6
    norm_num [Witness.rnanorm, decimalValue, abs_le]
    constructor <;> linarith [h.1, h.2]

theorem tightAccuracyFails_holds : tightAccuracyFails := by
  refine ⟨Witness.matrix, Witness.edger, Witness.rnanorm,
    Witness.counts_eq, Witness.edger_eq, Witness.rnanorm_eq, Witness.matrix_ok, ?_, ?_⟩
  all_goals
    have h := Numeric.factor2
    norm_num [Witness.edger, Witness.rnanorm, decimalValue]
    apply lt_of_lt_of_le ?_ (neg_le_abs _)
    linarith [h.1, h.2]

end Proofs
