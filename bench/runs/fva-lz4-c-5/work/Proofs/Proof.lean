import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate
import Proofs.Trace
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.all false
namespace Proofs

theorem no_step_values {H : HostSem} {s : Store} {f : Frame} {vs : List Val}
    {c : Config} : ¬ Step H ⟨s, f, vals vs⟩ c := by
  intro h
  have hu : seqUnique s f [] (vals vs ++ []) = true := by
    rw [seqUnique_vals]; rfl
  have hc := seq_complete h [] [] hu
  simp only [List.append_nil, seq_values, reduceCtorEq, or_self] at hc

theorem steps_values_end {H : HostSem} {s : Store} {f : Frame} {vs : List Val}
    {c : Config} (h : Steps H ⟨s, f, vals vs⟩ c) : c = ⟨s, f, vals vs⟩ := by
  cases h.cases_head with
  | inl he => exact he.symm
  | inr hs => obtain ⟨_, hs, _⟩ := hs; exact absurd hs no_step_values


theorem must_returns_post {H : HostSem} {P : Store → List Val → Prop} {c : Config}
    (hm : Must H (fun | .returned s vs => P s vs | .trapped _ => False) c)
    {s : Store} {f : Frame} {vs : List Val}
    (hs : Steps H c ⟨s, f, vals vs⟩) : P s vs := by
  generalize he : Config.mk s f (vals vs) = target at hs
  induction hm with
  | @done c o hf hq =>
    cases o with
    | trapped st => exact False.elim hq
    | returned st ws =>
      obtain ⟨hcstore, hcinstrs⟩ := hf
      obtain ⟨cs, cf, ci⟩ := c
      simp only [Config.store, Config.instrs] at hcstore hcinstrs
      subst cs ci
      have ht := steps_values_end hs
      rw [← he] at ht
      have htstore := congrArg Config.store ht
      have htvals := congrArg Config.instrs ht
      simp only [Config.store] at htstore
      simp only [Config.instrs, vals_inj] at htvals
      subst s vs
      exact hq
  | @next c hex hall ih =>
    cases hs.cases_head with
    | inl hc =>
      subst target
      subst c
      obtain ⟨c', hc'⟩ := hex
      exact False.elim (no_step_values hc')
    | inr hc =>
      obtain ⟨c', hstep, hrest⟩ := hc
      exact ih c' hstep hrest

noncomputable def allocated := allocModule {} Proofs.Lifted.module [] [.i32 65536] []
noncomputable def initializedMemory : MemInst :=
  ((Lifted.module.datas.headD ⟨[], .passive⟩).init.zipIdx).foldl
    (fun m bi => m.write (65536 + bi.2) 1 bi.1.toNat)
    { pages := 32, max := some 32, byte := fun _ => 0 }
noncomputable def canonical : Store × ModuleInst :=
  ({ allocated.1 with mems := [initializedMemory], datas := [⟨[]⟩] }, allocated.2)
theorem canonical_instance (H : HostSem) :
    Instance Proofs.Lifted.module H canonical.1 canonical.2 := by
  apply instantiate_sound (fuel := 400) (by simp [ImportsMatch, Proofs.Lifted.module])
  kernel_rfl

theorem init_returns (H : HostSem) :
    Must H (fun | .returned s vs => s = canonical.1 ∧ vs = [] | .trapped _ => False)
      ⟨allocated.1, ⟨[], allocated.2⟩, (initCode Proofs.Lifted.module).map .plain⟩ := by
  apply must_returned_of_runDet (n := 400)
    (s' := canonical.1) (f' := ⟨[], allocated.2⟩) (vs := [])
  · kernel_rfl
  · exact ⟨rfl, rfl⟩

theorem instance_unique {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Proofs.Lifted.module H s inst) :
    s = canonical.1 ∧ inst = canonical.2 := by
  obtain ⟨_, gvals, erefs, sa, ha, hgv, her, hrun⟩ := h
  change List.Forall₂ _ [] erefs at her
  cases her
  change List.Forall₂ _ [_] gvals at hgv
  cases hgv with
  | cons hv hnil =>
    cases hnil
    rename_i v
    change Steps H ⟨sa, ⟨[], inst⟩, vals [.i32 65536]⟩
      ⟨sa, ⟨[], inst⟩, vals [v]⟩ at hv
    have hvv := steps_values_end hv
    have hvv := congrArg Config.instrs hvv
    simp only [Config.instrs, vals_inj, List.cons.injEq, and_true] at hvv
    subst v
    change allocated = (sa, inst) at ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha.symm
    have hresult := must_returns_post (vs := []) (init_returns H) hrun
    exact ⟨hresult.1, by kernel_rfl⟩


noncomputable def caseStart (src dst : Nat) (input : List UInt8) (capacity : Nat) : Config :=
  invokeConfig (prepared canonical.1 src dst capacity input) 2
    (arguments src dst input.length capacity)

noncomputable def caseEnd (src dst : Nat) (input : List UInt8) (capacity fuel : Nat) : Config :=
  (runDet fuel (caseStart src dst input capacity)).getD (caseStart src dst input capacity)

noncomputable def canonicalMem : MemInst :=
  canonical.1.mems[0]?.getD { pages := 32, max := some 32, byte := fun _ => 0 }
theorem canonical_mem : canonical.1.mems[0]? = some canonicalMem := by kernel_rfl
theorem canonical_mem_size : canonicalMem.size = 2097152 := by kernel_rfl
def decoderType : FuncType := ⟨List.replicate 4 (.num .i32), [.num .i32]⟩
theorem canonical_func : canonical.1.funcs[2]? =
    some (.wasm decoderType canonical.2 Lifted.func2) := by kernel_rfl

set_option maxHeartbeats 200000 in
theorem checked_case {src dst capacity fuel : Nat} {input output : List UInt8}
    {result : BitVec 32}
    (hdomain : 131072 ≤ src ∧ src + input.length ≤ 2097152 ∧
      131072 ≤ dst ∧ dst + capacity ≤ 2097152 ∧
      (src + input.length ≤ dst ∨ dst + capacity ≤ src))
    (hr : runDet fuel (caseStart src dst input capacity) =
      some (caseEnd src dst input capacity fuel))
    (hv : (caseEnd src dst input capacity fuel).instrs = vals [.i32 result])
    (hb : bytesAt (caseEnd src dst input capacity fuel).store dst output.length = some output)
    (ht : checkTrace src dst input.length capacity fuel (caseStart src dst input capacity) = true) :
    CheckedCase src dst input capacity result output := by
  obtain ⟨hsrc, hsEnd, hdst, hdEnd, hdisjoint⟩ := hdomain
  refine ⟨hsrc, hsEnd, hdst, hdEnd, hdisjoint, ?_, ?_⟩
  · intro H; exact ⟨canonical.1, canonical.2, canonical_instance H⟩
  · intro H s inst hi
    have hu := instance_unique (H := H) (s := s) (inst := inst) hi
    rw [hu.1, hu.2]
    have hFits : ∀ p n, p + n ≤ 2097152 → Fits canonical.1 p n := by
      intro p n hpn
      exact ⟨canonicalMem, canonical_mem, canonical_mem_size.symm ▸ hpn⟩
    refine ⟨hFits _ _ hsEnd, hFits _ _ hdEnd, ?_, ?_⟩
    · have hf : (prepared canonical.1 src dst capacity input).funcs[2]? =
        some (.wasm decoderType canonical.2 Lifted.func2) := by
          simp only [prepared, Store.withBytes_funcs]
          exact canonical_func
      refine ⟨2, by kernel_rfl, ?_, ?_⟩
      · refine ⟨_, hf, ?_⟩
        simp [arguments, Val.HasType, FuncInst.type, decoderType]
      · have hc : runDet fuel (caseStart src dst input capacity) =
          some ⟨(caseEnd src dst input capacity fuel).store,
            (caseEnd src dst input capacity fuel).frame, vals [.i32 result]⟩ := by
          rw [← hv]; exact hr
        exact must_returned_of_runDet hc ⟨rfl, hb⟩
    · intro a ha
      have he : canonical.2.exportFunc "LZ4_decompress_safe" = some 2 := by kernel_rfl
      rw [he] at ha
      cases ha
      exact checkTrace_sound ht

end Proofs
