import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Numerics.Arith
import FVA.Proof.Numerics.Adequacy

namespace Proofs
open FVA.Wasm FVA.Wasm.Num
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem mul_checked (a b out : FVal)
    (ha : a.WF f64fmt) (hb : b.WF f64fmt) (hn : ¬ out.IsNaN)
    (hc : Impl.fmul f64fmt a b = out) :
    fmul f64fmt a b = {out} := by
  have hm : out ∈ fmul f64fmt a b := hc ▸ fmul_mem f64fmt_sane ha hb
  apply Set.ext
  intro z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (fmul_det f64fmt_sane a b out hm z hz hn).symm
  · intro hz
    exact Set.mem_singleton_iff.mp hz ▸ hm

private theorem div_checked (a b out : FVal)
    (ha : a.WF f64fmt) (hb : b.WF f64fmt) (hn : ¬ out.IsNaN)
    (hc : Impl.fdiv f64fmt a b = out) :
    fdiv f64fmt a b = {out} := by
  have hm : out ∈ fdiv f64fmt a b := hc ▸ fdiv_mem f64fmt_sane ha hb
  apply Set.ext
  intro z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr (fdiv_det f64fmt_sane a b out hm z hz hn).symm
  · intro hz
    exact Set.mem_singleton_iff.mp hz ▸ hm

theorem artifact_arithmetic_holds : artifact_arithmetic := by
  constructor
  · decide +kernel
  · rfl

theorem overflow_witness_holds : overflow_witness := by
  refine ⟨artifact_arithmetic_holds, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.IsNum]
  · norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.toReal]
  · have hp : (dbl 0x7fb0000000000000).toReal f64fmt ≠ 0 := by
      norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.toReal]
    rw [div_self hp, one_mul]
  · apply mul_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel
  · apply div_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel

theorem threshold_witness_holds : threshold_witness := by
  refine ⟨artifact_arithmetic_holds, ?_, ?_, ?_, ?_, ?_⟩
  · apply mul_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel
  · apply div_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel
  · apply div_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel
  · apply mul_checked
    all_goals first
      | exact ofBits_wf f64fmt_sane _
      | (norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax, FVal.WF, FVal.IsNaN]; done)
      | decide +kernel
  · norm_num [dbl, ofBits, f64fmt, FloatFormat.N, FloatFormat.emax,
      FVal.toReal]

end Proofs
