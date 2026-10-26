import FVATest.Subjects.EdgerCpm.LoaderMemory

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

attribute [local irreducible] initPrefix afterData allocation globalValues elementValues

-- Only the start function's 232-byte fill remains after the symbolic data-segment copy.
theorem initFinal_some : (run 1000 afterData).isSome := by decide +kernel
noncomputable def initFinal : Config := (run 1000 afterData).get initFinal_some

theorem initFinal_eq : run 1000 afterData = some initFinal := (Option.some_get initFinal_some).symm

attribute [local irreducible] initFinal

theorem initFinal_instrs : initFinal.instrs = [] := by kernel_rfl

theorem initFinal_frame : initFinal.frame = ⟨[], allocation.2⟩ := by kernel_rfl

theorem initialized (H : HostSem) :
    Instantiated H Lifted.module env imports initFinal.store allocation.2 := by
  refine ⟨env_matches, globalValues, elementValues, allocation.1, ?_, ?_, ?_, ?_⟩
  · kernel_rfl
  · apply (forall₂_mapM globals_eq).imp
    intro g v hv
    exact evalConst_sound hv
  · apply (forall₂_mapM elements_eq).imp
    intro e rs hers
    apply (forall₂_mapM hers).imp
    intro ex r hex
    simp only [bind, Option.bind_eq_some_iff] at hex
    rcases hex with ⟨v, hv, hvr⟩
    cases v <;> simp only [asRef, reduceCtorEq, Option.some.injEq] at hvr
    subst r
    exact evalConst_sound hv
  · have hp : Steps H initConfig initPrefix :=
      steps_of_walk initPrefix_eq
    have hf : Steps H afterData initFinal :=
      (run_sound initFinal_eq).1
    have hall := hp.trans ((initData_steps H).trans hf)
    have he : initFinal = ⟨initFinal.store, ⟨[], allocation.2⟩, []⟩ := by
      rw [← initFinal_instrs, ← initFinal_frame]
    rw [he] at hall
    exact hall

end Subjects.EdgerCpm.Existence
