import FVA.Proof.Exec.System
import FVA.Proof.Lib.Instance
import FVA.Lifted

/-!
# Exception examples (contract U28b T4)

`caught`: `thrower` throws from inside two blocks; the exception leaves both blocks, the
function's label and frame, the operand left below the call and the `try_table` body's label,
reaches the enclosing handler, matches its first clause and branches with its payload to the block
around the `try_table`; the code after that block adds the payload to an operand saved before the
`try_table`. Kernel-checked total correctness for every host: the call returns 142, and the final
store is the initial one with the thrown exception appended. `caughtSys`: the same call as a
process, under either growth policy (`sysMust_of_runDet`: throw normalization + clause selection
inside the process relation). `uncaught`, `uncaughtSys`: a throw no handler encloses ends every
execution with that exception (`Outcome.thrown`), a process abnormally.
-/

namespace FVA.Wasm.Exec.EHExamples

open FVA.Wasm FVA.Wasm.Exec Ref

/-- `[i32] → []`: the tag's type and `thrower`'s. -/
def i32T : FuncType := ⟨[.num .i32], []⟩
/-- `[] → [i32]`. -/
def mainT : FuncType := ⟨[], [.num .i32]⟩

/-- Functions 0 (`thrower`), 1 (`main`), 2 (`uncaught`); tag 0. -/
def inst : ModuleInst :=
  { types := [⟨[i32T], 0⟩, ⟨[mainT], 0⟩], funcs := [0, 1, 2], tags := [0] }

/-- `thrower x`: throws tag 0 with `x + 1` from inside two blocks. -/
def throwerBody : Expr :=
  [.block .empty [.block .empty [.localGet 0, .iconst .w32 1, .ibinop .w32 .add, .throw 0]]]

/-- `main`: `100`, then a block around a `try_table` whose tag-0 clause branches to that block
with the payload; the body leaves `5` below the call that throws; after the block, `i32.add`. -/
def mainBody : Expr :=
  [.iconst .w32 100,
    .block (.val (.num .i32))
      [.tryTable .empty [.tag 0 0] [.iconst .w32 5, .iconst .w32 41, .call 0, .drop],
        .iconst .w32 0],
    .ibinop .w32 .add]

/-- `uncaught`: `thrower 7`, no handler. -/
def uncaughtBody : Expr := [.iconst .w32 7, .call 0, .iconst .w32 0]

/-- Tag 0 of type `i32T`; the three functions. -/
def store : Store :=
  { tags := [⟨⟨[i32T], 0⟩⟩],
    funcs := [.wasm ⟨[i32T], 0⟩ inst ⟨0, [], throwerBody⟩,
      .wasm ⟨[mainT], 0⟩ inst ⟨1, [], mainBody⟩,
      .wasm ⟨[mainT], 0⟩ inst ⟨1, [], uncaughtBody⟩] }

/-- `store` with the exception of tag 0 and payload `v` appended. -/
def thrown (v : BitVec 32) : Store := { store with exns := [⟨0, [.i32 v]⟩] }

theorem caught_run :
    runDet 100 (invokeConfig store 1 []) = some ⟨thrown 42, ⟨[], {}⟩, vals [.i32 142]⟩ := by
  kernel_rfl

/-- `main` returns 142 for every host; its final store = `store` + the caught exception. -/
theorem caught (H : HostSem) :
    Must H (fun | .returned s vs => s = thrown 42 ∧ vs = [.i32 142] | _ => False)
      (invokeConfig store 1 []) := by
  refine runDet_must caught_run ?_
  rintro (⟨s, vs⟩ | s | ⟨s, a⟩) ⟨hs, hi⟩
  · exact ⟨hs.symm, (vals_inj.mp hi).symm⟩
  · exact vals_ne_trap _ hi
  · exact vals_ne_throwing _ _ hi

/-- `main` as a live process, under either growth policy: it returns 142, its world kept. -/
theorem caughtSys (W : World) (fits : Bool) (σ : W.St) (hl : W.exited σ = none) :
    SysMust W fits
      (fun | .returned τ s vs => τ = σ ∧ s = thrown 42 ∧ vs = [.i32 142] | _ => False)
      (σ, invokeConfig store 1 []) := by
  refine sysMust_of_runDet hl caught_run ?_
  rintro (⟨τ, s, vs⟩ | ⟨τ, s, k⟩ | ⟨τ, s⟩) hf
  · obtain ⟨hτ, -, hs, hi⟩ := hf
    exact ⟨hτ, hs.symm, (vals_inj.mp hi).symm⟩
  · obtain ⟨-, he, -⟩ := hf
    rw [hl] at he
    cases he
  · obtain ⟨-, -, ⟨-, hi⟩ | ⟨a, -, hi⟩⟩ := hf
    · exact vals_ne_trap _ hi
    · exact vals_ne_throwing _ _ hi

theorem uncaught_run :
    runDet 100 (invokeConfig store 2 []) = some ⟨thrown 8, ⟨[], {}⟩, throwing 0⟩ := by
  kernel_rfl

/-- `uncaught` ends every execution with exception 0 (tag 0, payload 8) in the store. -/
theorem uncaught (H : HostSem) :
    Must H (fun | .thrown s a => s = thrown 8 ∧ a = 0 | _ => False)
      (invokeConfig store 2 []) := by
  refine runDet_must uncaught_run ?_
  rintro (⟨s, vs⟩ | s | ⟨s, a⟩) ⟨hs, hi⟩
  · exact vals_ne_throwing _ _ hi.symm
  · simp [throwing] at hi
  · simp only [throwing, List.cons.injEq, AInstr.refExnAddr.injEq] at hi
    exact ⟨hs.symm, hi.1.symm⟩

/-- `uncaught` as a live process, under either growth policy: it finishes abnormally, its world
kept. -/
theorem uncaughtSys (W : World) (fits : Bool) (σ : W.St) (hl : W.exited σ = none) :
    SysMust W fits (fun | .abnormal τ s => τ = σ ∧ s = thrown 8 | _ => False)
      (σ, invokeConfig store 2 []) := by
  refine sysMust_of_runDet hl uncaught_run ?_
  rintro (⟨τ, s, vs⟩ | ⟨τ, s, k⟩ | ⟨τ, s⟩) hf
  · obtain ⟨-, -, -, hi⟩ := hf
    exact vals_ne_throwing _ _ hi.symm
  · obtain ⟨-, he, -⟩ := hf
    rw [hl] at he
    cases he
  · obtain ⟨hτ, -, ⟨hs, -⟩ | ⟨a, hs, -⟩⟩ := hf
    · exact ⟨hτ, hs.symm⟩
    · exact ⟨hτ, hs.symm⟩

end FVA.Wasm.Exec.EHExamples
