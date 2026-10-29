import Proofs.Instantiation
import Proofs.Determinism
import FVA.Proof.Valid.InstantiateConst

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Proofs.Execution

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem instance_unique {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) : s = freshStore ∧ inst = allocation.2 := by
  obtain ⟨_, gvals, erefs, s₁, ha, hgv, her, hrun⟩ := h
  have hglobals : Lifted.module.globals =
      [⟨⟨.var, .num .i32⟩, [.iconst .w32 65536]⟩] := rfl
  rw [hglobals] at hgv
  cases hgv with
  | cons hvalue htail =>
    cases htail
    have hvalue' := FVA.Wasm.Valid.InitProof.steps_values (vs := [.i32 65536]) hvalue
    have hbits := congrArg Config.instrs hvalue'
    have hv := Val.instr_inj.mp (List.singleton_inj.mp hbits)
    subst hv
    have helems : Lifted.module.elems = [] := rfl
    rw [helems] at her
    cases her
    have ha' : allocation = (s₁, inst) := ha
    have hs₁ := congrArg Prod.fst ha'
    have hi := congrArg Prod.snd ha'
    dsimp only [Prod.fst, Prod.snd] at hs₁ hi
    subst s₁ inst
    have hfinal := walk_to_empty_unique initial_walk fresh_instrs rfl hrun
    exact ⟨(congrArg Config.store hfinal).trans fresh_store, rfl⟩

end Proofs.Execution
