import FVATest.Subjects.Lz4C.Loop
import FVATest.Subjects.Lz4C.Instance

/-!
# R1 from the cutpoint statements (contract U20)

The prepared fresh instance (`store0` + the source and destination bytes), the export lookup and
the entry code lead to the main loop (`Loop.lean`), so every call returns one `i32`, reading and
writing only R1's sets. Conditional on `Entry`, `ShortcutS5`, `SegA`…`SegD` and `ErrRet` (proof
support; outside the review surface).
-/

namespace Subjects.Lz4C.Top

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Subjects.Lz4C

theorem steps_of_runDet {H : HostSem} {n : Nat} {c c' : Config} {vs : List Val}
    (hr : runDet n c = some c') (hv : c'.instrs = vals vs) : Steps H c c' := by
  induction n generalizing c with
  | zero => simp only [runDet, reduceCtorEq] at hr
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true] at hr
      have hi := congrArg (fun x => x.instrs) (Option.some.inj hr)
      exact False.elim ((vals_ne_trap vs) (hv.symm.trans hi.symm))
    | false =>
      simp only [runDet, ht, Bool.cond_false] at hr
      cases hu : uniqueStep c with
      | false => simp only [hu, Bool.cond_false, reduceCtorEq] at hr
      | true =>
        simp only [hu, Bool.cond_true] at hr
        cases hs : seq c.store c.frame [] c.instrs with
        | step s f es =>
          simp only [hs] at hr
          exact Relation.ReflTransGen.head (step_sound (by simp only [step, hs])) (ih hr)
        | final =>
          simp only [hs] at hr
          cases Option.some.inj hr
          exact .refl
        | _ => simp only [hs, reduceCtorEq] at hr

attribute [local irreducible] alloc initConfig in
theorem init_run : runDet 1000 initConfig = some ⟨store0, ⟨[], alloc.2⟩, []⟩ := by
  have hf : ((runDet 1000 initConfig).get init_some).frame = ⟨[], alloc.2⟩ := by kernel_rfl
  exact (Option.some_get init_some).symm.trans (congrArg some
    ((congrArg (fun f => Config.mk store0 f ((runDet 1000 initConfig).get init_some).instrs)
      hf).trans (congrArg (fun es => Config.mk store0 ⟨[], alloc.2⟩ es) init_instrs)))

/-- `store0` with `alloc.2` is a fresh instance. -/
theorem instance0 (H : HostSem) : Instance Lifted.module H store0 alloc.2 := by
  refine ⟨?_, [.i32 65536], [], alloc.1, rfl, ?_, ?_, ?_⟩
  · exact .nil
  · exact .cons .refl .nil
  · exact .nil
  · exact steps_of_runDet (vs := []) init_run rfl

end Subjects.Lz4C.Top
