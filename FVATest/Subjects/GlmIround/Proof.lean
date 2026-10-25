import FVATest.Subjects.GlmIround.Spec
import FVA.Proof.Lib.Instance

/-! Proof of the GLM `iround` counterexample (contract U14 S5). The run is four instructions; the
return value closes by `decide +kernel`/`kernel_rfl` on the reference interpreter, the real-value
bound by reducing the bit pattern to its `FVal`. -/

namespace Subjects.GlmIround

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxRecDepth 100000

noncomputable def alloc : Store × ModuleInst := allocModule {} Lifted.module [] [] []
noncomputable def cfg : Config := invokeConfig alloc.1 0 [.f64 belowHalf]
theorem runSome : (runDet 50 cfg).isSome := by decide +kernel

/-- `belowHalf` is the normal number `(1 + (2^52 − 1)/2^52) · 2^⁻²`. -/
theorem ofBits_belowHalf : ofBits f64fmt belowHalf = FVal.normal false 4503599627370495 (-2) := by
  unfold ofBits f64fmt
  norm_num [FloatFormat.N, FloatFormat.M, FloatFormat.E, FloatFormat.emax, belowHalf]

theorem belowHalf_real : (ofBits f64fmt belowHalf).toReal f64fmt ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
  rw [ofBits_belowHalf]
  unfold FVal.toReal f64fmt
  norm_num

theorem iround_breaks_holds : Subjects.GlmIround.iround_breaks := by
  refine ⟨⟨instantiable_alloc rfl rfl rfl rfl rfl, ?_⟩, belowHalf_real⟩
  rintro H s inst hinst
  obtain ⟨h1, h2⟩ := Prod.mk.inj (instance_alloc rfl rfl rfl rfl hinst)
  subst h1; subst h2
  refine ⟨0, by decide +kernel, ⟨_, rfl, .cons ⟨⟩ .nil⟩, ?_⟩
  refine (must_returned_of_runDet_get (P := fun _ _ => True) (vs := [.i32 1]) (n := 50) runSome
    (by kernel_rfl) trivial).mono ?_
  rintro (⟨s', vs⟩ | s') h
  · exact h.1
  · exact h

end Subjects.GlmIround
