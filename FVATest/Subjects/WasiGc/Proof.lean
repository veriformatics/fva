import FVATest.Subjects.WasiGc.Spec
import FVA.Proof.Wasi.Canonical
import FVA.Proof.Valid.Validator
import FVA.Proof.Exec.Imports
import FVA.Proof.Wasi.WfRun

/-! Proof of `countsGC`: the module instantiates on the machine (`instantiateU`), the whole process
run from `start` — 1,655 steps, five of them host calls (`path_open`, two `fd_read`, `fd_write`,
`proc_exit`) answered by the executable WASI host — is one evaluated `sysRun` (the kernel reduces
it in `run_exits` + `run_stdout`), and `launch_sysMust` carries its exit to every launch. -/

namespace Subjects.WasiGc

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasi

/-- The start world is well formed (U29a T7: every initial world a claim starts from is checked). -/
theorem start_wf : start.Wf := by decide

theorem instU :
    (instantiateU 100 (hostMStore Lifted.module) Lifted.module (hostImports Lifted.module)).isSome =
      true := by
  decide +kernel

/-- The machine store + instance every launch starts from. -/
noncomputable def inst : MStore × ModuleInst :=
  (instantiateU 100 (hostMStore Lifted.module) Lifted.module (hostImports Lifted.module)).get instU

theorem inst_eq :
    instantiateU 100 (hostMStore Lifted.module) Lifted.module (hostImports Lifted.module) =
      some inst := by
  simp [inst]

theorem start_export : inst.2.exportFunc "_start" = some 4 := by decide +kernel

theorem memory_export : inst.2.exportMem "memory" = some 0 := by decide +kernel

/-- The process run from `start`, past its exit. -/
noncomputable def run : State × MState × Bool :=
  sysRun State.exited (wasiHost Lifted.module 0 none) 2000 (start, MState.ofInvoke inst.1 4 [])

theorem run_exits : run.1.exited = some 0 := by decide +kernel

theorem run_stdout : run.1.stdout = report seq := by decide +kernel

/-- The report for the committed input, concretely (`Neg/Byte`'s positive control). -/
theorem report_seq : report seq = ascii "8 17\n" := by decide +kernel

theorem valid : Valid.ModuleValid Lifted.module := Valid.validate_sound (by decide +kernel)

theorem launches : ∃ c mem, Launch Lifted.module "_start" [] c mem := by
  have hm : ImportsMatch (hostStore Lifted.module) Lifted.module (hostImports Lifted.module) :=
    (Ref.importsMatch_iff _ _ _).mp (by decide +kernel)
  -- `FuncInst` has no decidable equality: decide a match on it instead
  have hchk : (match inst.1.abs.funcs[4]? with
      | some fi => (match fi.type.expand with | some ⟨[], []⟩ => true | _ => false)
      | none => false) = true := by decide +kernel
  refine ⟨_, _, launch_of_instantiateU inst_eq valid (by decide +kernel) (by decide +kernel) ?_ ?_
    hm start_export memory_export ?_⟩
  · intro im h
    have hall : Lifted.module.imports.all (fun im => match im.desc with
        | .func _ => true
        | _ => false) = true := by decide +kernel
    have him := List.all_eq_true.mp hall im h
    cases hd : im.desc <;> simp_all
  · intro id im h _ _
    have : ∀ id < Lifted.module.imports.length, (bind Lifted.module id).isSome = true := by
      decide +kernel
    exact this id (List.getElem?_eq_some_iff.mp h).1
  · split at hchk
    · rename_i fi hfi
      refine ⟨fi, ⟨[], []⟩, hfi, ?_, List.Forall₂.nil⟩
      split at hchk
      · assumption
      · simp at hchk
    · simp at hchk

theorem countsGC_proof : countsGC := by
  refine ⟨launches, fun c mem hl => ?_⟩
  -- eta on a variable triple: the run itself stays unevaluated here
  have eta : ∀ p : State × MState × Bool, p = (p.1, p.2.1, p.2.2) := fun _ => rfl
  have hrun : sysRun State.exited (wasiHost Lifted.module 0 none) 2000
      (start, MState.ofInvoke inst.1 4 []) = (run.1, run.2.1, run.2.2) := eta run
  -- the restricted world's `exited` = `State.exited`, as functions: `run` stays unevaluated
  have hex : ((world Lifted.module 0).restrict (E Lifted.module 0)).exited = State.exited := rfl
  have he : ((world Lifted.module 0).restrict (E Lifted.module 0)).exited run.1 = some 0 := by
    rw [hex]; exact run_exits
  exact launch_sysMust inst_eq start_export memory_export hrun
    (sysMust_exited he ⟨run.1, _, rfl, run_stdout⟩) c mem hl

end Subjects.WasiGc
