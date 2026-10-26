import Proofs.Spec
import FVA.Proof.Lib

/-! Proofs: one theorem per claim, typed by the claim constant (`theorem answer_holds :
answer := …`). Nobody reads this file; `fva trust` checks it. -/

namespace Proofs

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem artifact_binding_holds : artifact_binding := by
  exact ⟨rfl, by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def checked (c : Config) (expected : Nat) : Bool :=
  (runDet 1000 c).any (fun cf => cf.instrs.isEmpty && outputBits cf.store == expected)

private theorem checked_sound (H : HostSem) (c : Config) (expected : Nat)
    (h : checked c expected = true) :
    Must H (fun | .returned s vs => vs = [] ∧ outputBits s = expected
                | .trapped _ => False) c := by
  unfold checked at h
  cases hr : runDet 1000 c with
  | none => simp [hr] at h
  | some cf =>
    have hx : cf.instrs = [] ∧ outputBits cf.store = expected := by
      simpa [hr, Bool.and_eq_true, List.isEmpty_iff] using h
    have he : cf = ⟨cf.store, cf.frame, vals []⟩ := by
      cases cf
      simp_all
    have hh := hr.trans (congrArg some he)
    exact must_returned_of_runDet hh ⟨rfl, hx.2⟩

private theorem fixture_call (H : HostSem) (c L expected : Nat)
    (hr : checked (invokeConfig (fixtureStore c L) 2 fixtureArgs) expected = true) :
    CallReturns H (fixtureStore c L) fixtureInstance "calc_cpm_raw" fixtureArgs
      (fun s vs => vs = [] ∧ outputBits s = expected) := by
  refine ⟨2, rfl, ?_, checked_sound H _ _ hr⟩
  refine ⟨.wasm ⟨[.num .i32, .num .i32, .num .i32, .num .i32], []⟩
      fixtureInstance (Lifted.module.funcs[86]?.getD { type := 0, locals := [], body := [] }),
    rfl, ?_⟩
  simp [fixtureArgs, FuncInst.type, Val.HasType]

theorem r1_overflow_holds : r1_overflow := by
  refine ⟨by decide +kernel, by positivity, ?_, ?_⟩
  · rw [div_self (by positivity : (2 : ℝ)^1023 ≠ 0), one_mul]
  intro H
  apply fixture_call H
  decide +kernel

theorem r2_cpm_bits_holds : r2_cpm_bits := by
  intro H
  apply fixture_call H
  decide +kernel

theorem r2_rounding_gap_holds : r2_rounding_gap := by
  refine ⟨r2_cpm_bits_holds, ?_, ?_, ?_⟩
  · intro H
    apply must_returned_of_runDet (n := 10) (s' := {}) (f' := ⟨[], {}⟩)
      (vs := [.f64 0x4120f4471c71c71d])
    · kernel_rfl
    · rfl
  · norm_num [Num.FVal.toReal, Num.ofBits, Num.f64fmt, Num.FloatFormat.N,
      Num.FloatFormat.emax]
  · norm_num [Num.FVal.toReal, Num.ofBits, Num.f64fmt, Num.FloatFormat.N,
      Num.FloatFormat.emax]

end Proofs
