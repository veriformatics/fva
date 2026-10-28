import Proofs.Lifted
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Valid.InstantiateConst

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def allocated : Store × ModuleInst :=
  allocModule {} Lifted.module [] [.i32 65536] []

noncomputable def initialized : Config :=
  (walk 130 ⟨allocated.1, ⟨[], allocated.2⟩, (initCode Lifted.module).map .plain⟩).getD
    ⟨{}, ⟨[], {}⟩, []⟩

theorem init_walk :
    walk 130 ⟨allocated.1, ⟨[], allocated.2⟩, (initCode Lifted.module).map .plain⟩ =
      some initialized := by kernel_rfl

theorem initialized_empty : initialized.instrs = [] := by kernel_rfl

theorem initialized_frame : initialized.frame = ⟨[], allocated.2⟩ := by kernel_rfl

theorem initialized_instance (H : HostSem) :
    Instance Lifted.module H initialized.store allocated.2 := by
  apply instantiate_sound (fuel := 1000) (by exact List.Forall₂.nil)
  kernel_rfl

private theorem walk_unique_empty {H : HostSem} {n : Nat} {c d e : Config}
    (hw : walk n c = some d) (hd : d.instrs = [])
    (he : e.instrs = []) (hs : Steps H c e) : e = d := by
  induction n generalizing c with
  | zero =>
    simp only [walk_zero, Option.some.injEq] at hw
    subst c
    obtain ⟨ds, df, es⟩ := d
    dsimp at hd
    subst es
    exact steps_nil hs
  | succ n ih =>
    cases hu : uniqueStep c <;> simp only [walk, hu, Bool.cond_false,
      Bool.cond_true, reduceCtorEq] at hw
    cases ht : step c with
    | none => simp [ht] at hw
    | some mid =>
      rw [ht, Option.bind_some] at hw
      rcases hs.cases_head with rfl | ⟨next, hnext, hrest⟩
      · have hn := step_sound (H := H) ht
        obtain ⟨es, ef, is⟩ := c
        dsimp at he
        subst is
        exact False.elim (no_step_nil hn)
      · have hm := step_complete hnext ht hu
        subst next
        exact ih hw hrest

theorem instance_unique {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) :
    s = initialized.store ∧ inst = allocated.2 := by
  obtain ⟨_, gvals, erefs, s₁, ha, hgv, her, hrun⟩ := h
  change List.Forall₂ _ [_] gvals at hgv
  cases hgv with
  | cons hv htail =>
    cases htail
    rename_i v
    have hsteps : Steps H ⟨s₁, ⟨[], inst⟩, vals [.i32 65536]⟩
        ⟨s₁, ⟨[], inst⟩, [v.instr]⟩ := hv
    have hv' := congrArg Config.instrs (FVA.Wasm.Valid.InitProof.steps_values hsteps)
    have hv'' : v = .i32 65536 := Val.instr_inj.mp (List.singleton_inj.mp hv')
    subst v
    change List.Forall₂ _ [] erefs at her
    cases her
    change allocated = (s₁, inst) at ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha
    have heq := walk_unique_empty init_walk initialized_empty rfl hrun
    exact ⟨congrArg Config.store heq, rfl⟩

def decoderType : FuncType :=
  ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩

theorem initialized_decoder : initialized.store.funcs[2]? =
    some (.wasm decoderType allocated.2 Lifted.func2) := by kernel_rfl

theorem initialized_export : allocated.2.exportFunc "LZ4_decompress_safe" = some 2 := by
  kernel_rfl

noncomputable def initialMem : MemInst :=
  initialized.store.mems[0]?.getD { pages := 0, max := none, byte := fun _ => 0 }

theorem initialMem_lookup : initialized.store.mems[0]? = some initialMem := by kernel_rfl

theorem initialMem_size : initialMem.size = 2097152 := by kernel_rfl

end Proofs
