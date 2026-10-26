import Proofs.Spec
import FVA.Proof.Lib

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def testStart : Config :=
  invokeConfig testStore 160 [.i32 32768, .i32 32800, .i32 32832, .i32 1]

def goodResult (c : Config) : Bool :=
  c.instrs.isEmpty && match c.store.mems[0]? with
    | some m => (List.range 8).map (fun k => m.byte (32832 + k)) == [0, 0, 0, 0, 0, 0, 240, 127]
    | none => false

def resultPost (s : Store) (vs : List Val) : Prop :=
  vs = [] ∧ ∃ m, s.mems[0]? = some m ∧
    (List.range 8).map (fun k => m.byte (32832 + k)) = [0, 0, 0, 0, 0, 0, 240, 127]

theorem good_sound (c : Config) (hg : goodResult c = true) :
    ∀ o, Final c o → (match o with
      | .returned s vs => resultPost s vs
      | .trapped _ => False) := by
  unfold goodResult at hg
  obtain ⟨he, hb⟩ := Bool.and_eq_true_iff.mp hg
  have hi : c.instrs = [] := List.isEmpty_iff.mp he
  cases hm : c.store.mems[0]? with
  | none => simp only [hm, Bool.false_eq_true] at hb
  | some m =>
    have hbits : (List.range 8).map (fun k => m.byte (32832 + k)) =
        [0, 0, 0, 0, 0, 0, 240, 127] := by
      simpa only [hm, beq_iff_eq] using hb
    rintro (⟨s, vs⟩ | s) ⟨hs, hv⟩
    · have hvs : vs = [] := vals_inj.mp (hv.symm.trans hi)
      subst vs
      exact ⟨rfl, m, hs ▸ hm, hbits⟩
    · rw [hi] at hv
      contradiction

theorem good_must {n : Nat} {c : Config} (H : HostSem)
    (hc : ((runDet n c).map goodResult).getD false = true) :
    Must H (fun | .returned s vs => resultPost s vs | .trapped _ => False) c := by
  cases hr : runDet n c with
  | none => simp only [hr, Option.map_none, Option.getD_none, Bool.false_eq_true] at hc
  | some d =>
    have hg : goodResult d = true := by
      simpa only [hr, Option.map_some, Option.getD_some] using hc
    exact runDet_must hr (good_sound d hg)

theorem test_checked : ((runDet 400 testStart).map goodResult).getD false = true := by
  kernel_rfl

theorem test_func : testStore.funcs[160]? =
    some (.wasm ⟨List.replicate 4 (.num .i32), []⟩ testInst Lifted.func86) := by
  kernel_rfl

theorem test_invoke : InvokeOK testStore 160
    [.i32 32768, .i32 32800, .i32 32832, .i32 1] := by
  refine ⟨_, test_func, ?_⟩
  exact .cons True.intro (.cons True.intro (.cons True.intro (.cons True.intro .nil)))

theorem test_export : ∃ e ∈ Lifted.module.exports,
    e.name = "calc_cpm_raw" ∧ e.desc = .func 160 := by
  exact ⟨⟨"calc_cpm_raw", .func 160⟩, by decide +kernel, rfl, rfl⟩

theorem r1_overflow_holds : r1_overflow := by
  refine ⟨test_export, rfl, rfl, ?_⟩
  intro H
  exact ⟨160, rfl, test_invoke, good_must H test_checked⟩

/-- The mathematical result for equal nonzero count and library size. -/
theorem equal_count_exact (c : ℝ) (hc : c ≠ 0) : c / c * 1000000 = 1000000 := by
  rw [div_self hc, one_mul]

end Proofs
