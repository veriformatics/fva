import FVA.Proof.Lib.Footprint

/-!
# Footprint witnesses (contract U19 A4)

A caller calls a callee that stores (or loads) the byte at address 100. `CallWithin` holds for a
footprint containing that byte and fails for one excluding it: the access happens inside the
callee's frame, so the rejections need the spec's `frame` + `label` context cases and the
checker's descent into frames (`writes_iff`, `reads_iff`).
-/

namespace FVA.Wasm.Exec.Ref.FootprintExamples

open FVA.Wasm FVA.Wasm.Exec

/-- The callee's body: stores 7 at address 100 (`i32.store8`). -/
def storeBody : List Instr := [.iconst .w32 100, .iconst .w32 7, .storePacked .w32 .p8 ⟨0, 0⟩]

/-- The callee's body: loads the byte at address 100 (`i32.load8_u`) and drops it. -/
def loadBody : List Instr := [.iconst .w32 100, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .drop]

/-- Function 0 (export `f`) calls function 1. -/
def inst : ModuleInst :=
  { types := [⟨[⟨[], []⟩], 0⟩], funcs := [0, 1], mems := [0], exports := [⟨"f", .func 0⟩] }

/-- The store: the caller, the callee with body `body`, one zeroed page of memory. -/
def store (body : List Instr) : Store :=
  { funcs := [.wasm ⟨[⟨[], []⟩], 0⟩ inst { type := 0, locals := [], body := [.call 1] },
      .wasm ⟨[⟨[], []⟩], 0⟩ inst { type := 0, locals := [], body := body }],
    mems := [{ pages := 1, max := none, byte := fun _ => 0 }] }

/-- The configuration just before the callee's access, under both frames. -/
def atAccess (body : List Instr) : Config :=
  ⟨store body, ⟨[], {}⟩, [.frame 0 ⟨[], inst⟩ [.label 0 [] [.frame 0 ⟨[], inst⟩
    [.label 0 [] (body.map .plain)]]]]⟩

theorem invokeOK (body : List Instr) : InvokeOK (store body) 0 [] :=
  ⟨_, _, rfl, rfl, .nil⟩

theorem walk_atAccess (body : List Instr) :
    walk 3 (invokeConfig (store body) 0 []) = some (atAccess body) := by
  rfl

theorem access_store : access (atAccess storeBody) = some ⟨true, 0, 100, 1⟩ := rfl

theorem access_load : access (atAccess loadBody) = some ⟨false, 0, 100, 1⟩ := rfl

/-- The store's footprint = the byte at address 100 of memory 0: every step, the callee's store
included, stays inside it. -/
theorem store_within (H : HostSem) :
    CallWithin H (store storeBody) inst "f" [] (fun _ _ => False)
      (fun ma a => ma = 0 ∧ a = 100) := by
  refine ⟨0, rfl, invokeOK _, ?_⟩
  have h : MustW H (fun _ _ => False) (fun ma a => ma = 0 ∧ a = 100) (fun _ => True)
      (Context.hole.fill (invokeConfig (store storeBody) 0 [])) := by
    unfold invokeConfig
    iterate 8 (wasm_cstepw [store, inst, storeBody, Val.intBits, MemInst.size,
        BitVec.toNat_ofNat]; first
      | exact within_of_access_none rfl
      | exact within_of_access rfl (fun h => absurd h (by decide))
          (fun _ a h₁ h₂ => ⟨rfl, by simp [PackSize.bits] at h₁ h₂; omega⟩))
    exact mustW_final (o := .returned _ []) ⟨rfl, rfl⟩ trivial
  exact h.2

/-- The load's footprint = the byte at address 100 of memory 0. -/
theorem load_within (H : HostSem) :
    CallWithin H (store loadBody) inst "f" [] (fun ma a => ma = 0 ∧ a = 100)
      (fun _ _ => False) := by
  refine ⟨0, rfl, invokeOK _, ?_⟩
  have h : MustW H (fun ma a => ma = 0 ∧ a = 100) (fun _ _ => False) (fun _ => True)
      (Context.hole.fill (invokeConfig (store loadBody) 0 [])) := by
    unfold invokeConfig
    iterate 9 (wasm_cstepw [store, inst, loadBody, MemInst.size, BitVec.toNat_ofNat,
        MemInst.read]; first
      | exact within_of_access_none rfl
      | exact within_of_access rfl (fun _ a h₁ h₂ => ⟨rfl, by simp [PackSize.bits] at h₁ h₂; omega⟩)
          (fun h => absurd h (by decide)))
    exact mustW_final (o := .returned _ []) ⟨rfl, rfl⟩ trivial
  exact h.2

/-- A footprint excluding address 100 is refuted by the reachable `Writes` inside the callee. -/
theorem store_not_within (H : HostSem) (R : Nat → Nat → Prop) :
    ¬ CallWithin H (store storeBody) inst "f" [] R (fun _ a => a ≠ 100) := by
  rintro ⟨a, ha, -, hth⟩
  obtain rfl : a = 0 := by simpa [ModuleInst.exportFunc, inst] using ha.symm
  exact (hth _ (steps_of_walk (walk_atAccess storeBody))).2 0 100
    (writes_iff.mpr ⟨_, access_store, rfl, rfl, le_rfl, by decide⟩) rfl

/-- A footprint excluding address 100 is refuted by the reachable `Reads` inside the callee. -/
theorem load_not_within (H : HostSem) (W : Nat → Nat → Prop) :
    ¬ CallWithin H (store loadBody) inst "f" [] (fun _ a => a ≠ 100) W := by
  rintro ⟨a, ha, -, hth⟩
  obtain rfl : a = 0 := by simpa [ModuleInst.exportFunc, inst] using ha.symm
  exact (hth _ (steps_of_walk (walk_atAccess loadBody))).1 0 100
    (reads_iff.mpr ⟨_, access_load, rfl, rfl, le_rfl, by decide⟩) rfl

end FVA.Wasm.Exec.Ref.FootprintExamples
