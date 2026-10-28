import Proofs.Spec
import FVA.Proof.Lib
import FVA.Proof.Exec.Instantiate

namespace Proofs
open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 1024

private theorem steps_values {H : HostSem} {s : Store} {f : Frame}
    {vs : List Val} {c : Config} (h : Steps H ⟨s, f, vals vs⟩ c) :
    c = ⟨s, f, vals vs⟩ := by
  have hn : ∀ c', ¬ Step H ⟨s, f, vals vs⟩ c' := by
    intro c' hs
    have hu : seqUnique s f [] (vals vs ++ []) = true := by
      rw [seqUnique_vals]; rfl
    have hc := seq_complete hs [] [] hu
    simp [seq_values] at hc
  induction h with
  | refl => rfl
  | tail h hs ih => subst_vars; exact False.elim (hn _ hs)

private theorem runDet_nil_unique {H : HostSem} {n : Nat} {c d : Config}
    (hr : runDet n c = some d) (hd : d.instrs = [])
    {s : Store} {f : Frame} (hs : Steps H c ⟨s, f, []⟩) :
    (⟨s, f, []⟩ : Config) = d := by
  induction n generalizing c with
  | zero => simp [runDet] at hr
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true, Option.some.injEq] at hr
      subst d
      cases hd
    | false =>
      cases hu : uniqueStep c with
      | false => simp [runDet, ht, hu] at hr
      | true =>
        simp only [runDet, ht, hu, Bool.cond_false, Bool.cond_true] at hr
        cases he : seq c.store c.frame [] c.instrs with
        | step s' f' es' =>
          simp only [he] at hr
          have hstep : step c = some ⟨s', f', es'⟩ := by simp only [step, he]
          rcases hs.cases_head with heq | ⟨mid, hfirst, hrest⟩
          · subst c
            exact False.elim (no_step_nil (step_sound (H := H) hstep))
          · have hm := step_complete hfirst hstep hu
            subst mid
            exact ih hr hrest
        | final =>
          simp only [he, Option.some.injEq] at hr
          subst d
          cases c with
          | mk cs cf ces =>
            change ces = [] at hd
            subst ces
            exact steps_nil hs
        | stuck => simp [he] at hr
        | br a b => simp [he] at hr
        | ret a => simp [he] at hr

private noncomputable def allocation := allocModule {} Lifted.module [] [.i32 65536] []
private noncomputable def initConfig : Config :=
  ⟨allocation.1, ⟨[], allocation.2⟩, (initCode Lifted.module).map .plain⟩
private noncomputable def initialized := (runDet 1024 initConfig).getD initConfig
private noncomputable def ready : Store × ModuleInst := (initialized.store, allocation.2)

private theorem init_finished : runDet 1024 initConfig = some initialized := by
  have h : (runDet 1024 initConfig).isSome = true := by decide +kernel
  cases he : runDet 1024 initConfig with
  | none => simp [he] at h
  | some a => simp [initialized, he]

private theorem initialized_instrs : initialized.instrs = [] := by
  have h : initialized.instrs.isEmpty = true := by decide +kernel
  simpa using h
private theorem initialized_frame : initialized.frame = ⟨[], allocation.2⟩ := by kernel_rfl

private theorem ready_instance (H : HostSem) : Instance Lifted.module H ready.1 ready.2 := by
  apply instantiate_sound (fuel := 1024)
  · exact List.Forall₂.nil
  · kernel_rfl

private theorem instance_unique {H : HostSem} {s : Store} {inst : ModuleInst}
    (h : Instance Lifted.module H s inst) : (s, inst) = ready := by
  obtain ⟨_, gvals, erefs, s₁, ha, hg, he, hs⟩ := h
  change List.Forall₂ _ [_] gvals at hg
  cases hg with
  | cons hv hnil =>
    cases hnil
    have hv' := steps_values (vs := [.i32 65536]) hv
    have hv'' := congrArg Config.instrs hv'
    have hval := Val.instr_inj.mp (List.cons.inj hv'').1
    cases hval
    change List.Forall₂ _ [] erefs at he
    cases he
    have ha' : allocation = (s₁, inst) := ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ha'.symm
    change Steps H initConfig ⟨s, ⟨[], allocation.2⟩, []⟩ at hs
    have hh := runDet_nil_unique (H := H) (c := initConfig) (d := initialized)
      (s := s) (f := ⟨[], allocation.2⟩) init_finished initialized_instrs hs
    have hstore := congrArg Config.store hh
    exact congrArg (fun st : Store => (st, allocation.2)) hstore

private def decoderType : FuncType :=
  ⟨[.num .i32, .num .i32, .num .i32, .num .i32], [.num .i32]⟩

private theorem ready_decoder : ready.1.funcs[2]? =
    some (.wasm decoderType allocation.2 Lifted.func2) := by kernel_rfl

private theorem ready_export : ready.2.exportFunc "LZ4_decompress_safe" = some 2 := by
  decide +kernel

private theorem empty_run (H : HostSem) (s : Store) (p q capacity : BitVec 32)
    (hf : s.funcs[2]? = some (.wasm decoderType allocation.2 Lifted.func2)) :
    Must H (fun | .returned s' vs => s' = s ∧ vs = [.i32 4294967295]
                | .trapped _ => False)
      (invokeConfig s 2 [.i32 p, .i32 q, .i32 0, .i32 capacity]) := by
  have hz : FVA.Wasm.Num.ieqz (0 : BitVec 32) ≠ 0 := by decide +kernel
  have hc0 : FVA.Wasm.Num.iltS (0 : BitVec 32) 0#32 = 0 := by decide +kernel
  have hne : FVA.Wasm.Num.ine (0 : BitVec 32) 1#32 ≠ 0 := by decide +kernel
  unfold invokeConfig
  by_cases hp : p = 0
  · subst p
    wasm_run [hf, Lifted.func2, decoderType, hz]
    exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  · have hpn : FVA.Wasm.Num.ieqz p = 0 := (FVA.Wasm.Num.ieqz_eq_zero p).mpr hp
    by_cases hn : capacity.slt 0
    · have hcn : FVA.Wasm.Num.iltS capacity 0#32 ≠ 0 := by
        intro he
        exact ((FVA.Wasm.Num.iltS_eq_zero capacity 0).mp he) hn
      wasm_run [hf, Lifted.func2, decoderType, hpn, hcn]
      exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    · have hcn : FVA.Wasm.Num.iltS capacity 0#32 = 0 :=
        (FVA.Wasm.Num.iltS_eq_zero capacity 0).mpr hn
      by_cases hc : capacity = 0
      · wasm_run [hf, Lifted.func2, decoderType, hpn, hcn, hc, hc0, hne]
        exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
      · wasm_run [hf, Lifted.func2, decoderType, hpn, hcn, hc, hz]
        exact Must.done (o := .returned s [.i32 4294967295]) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

private noncomputable def startCase (c : Case) : Config :=
  invokeConfig (prepared ready.1 c) 2
    [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 c.input.length),
     .i32 (BitVec.ofNat 32 c.capacity)]

private def observation (c : Case) (d : Config) :=
  (d.instrs.map toVal, bytesAt d.store 196608 c.output.length,
   bytesAt d.store 131072 c.input.length, bytesAt d.store 196600 8,
   bytesAt d.store (196608 + c.capacity) 8)

private def expected (c : Case) :=
  ([some (Val.i32 (BitVec.ofInt 32 c.result))], some c.output, some c.input,
   some (List.replicate 8 (165 : UInt8)), some (List.replicate 8 (165 : UInt8)))

private noncomputable def computedCase (c : Case) (fuel : Nat) : Prop :=
  (runDet fuel (startCase c)).map (observation c) = some (expected c)

private theorem instrs_of_observation {es : List AInstr} {v : Val}
    (h : es.map toVal = [some v]) : es = vals [v] := by
  cases es with
  | nil => cases h
  | cons a es =>
    have ⟨ha, ht⟩ := List.cons.inj h
    have hn : es = [] := List.eq_nil_of_length_eq_zero (by
      have hh := congrArg List.length ht
      simpa using hh)
    subst es
    rw [eq_instr_of_toVal ha]
    rfl

private theorem prepared_funcs (s : Store) (c : Case) :
    (prepared s c).funcs = s.funcs := by
  simp only [prepared, Store.withBytes_funcs]

private theorem computed_returns (c : Case) (fuel : Nat) (H : HostSem)
    (hc : computedCase c fuel) :
    CallReturns H (prepared ready.1 c) ready.2 "LZ4_decompress_safe"
      [.i32 131072, .i32 196608, .i32 (BitVec.ofNat 32 c.input.length),
       .i32 (BitVec.ofNat 32 c.capacity)] fun s' vs =>
      vs = [.i32 (BitVec.ofInt 32 c.result)] ∧
      bytesAt s' 196608 c.output.length = some c.output ∧
      bytesAt s' 131072 c.input.length = some c.input ∧
      bytesAt s' 196600 8 = some (List.replicate 8 165) ∧
      bytesAt s' (196608 + c.capacity) 8 = some (List.replicate 8 165) := by
  refine ⟨2, ready_export, ?_, ?_⟩
  · refine ⟨.wasm decoderType allocation.2 Lifted.func2, ?_, ?_⟩
    · have he := prepared_funcs ready.1 c
      exact (congrArg (fun fs : List FuncInst => fs[2]?) he).trans ready_decoder
    · simp [Val.HasType, FuncInst.type, decoderType]
  · unfold computedCase at hc
    cases hr : runDet fuel (startCase c) with
    | none => simp [hr] at hc
    | some d =>
      simp only [hr, Option.map_some, Option.some.injEq] at hc
      have hobs := Prod.mk.inj hc
      have hins := instrs_of_observation hobs.1
      apply must_returned_of_runDet (s' := d.store) (f' := d.frame)
        (vs := [.i32 (BitVec.ofInt 32 c.result)])
      · change runDet fuel (startCase c) = _
        rw [hr]
        congr 1
        cases d
        simp_all only []
      · exact ⟨rfl, (Prod.mk.inj hobs.2).1,
          (Prod.mk.inj (Prod.mk.inj hobs.2).2).1,
          (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hobs.2).2).2).1,
          (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj hobs.2).2).2).2⟩

private theorem case_of_computation (c : Case) (fuel : Nat)
    (hc : computedCase c fuel) : caseCorrect c := by
  intro H s inst hinst
  have he := instance_unique hinst
  have hh := computed_returns c fuel H hc
  have hs : ready.1 = s := (congrArg Prod.fst he).symm
  have hi : ready.2 = inst := (congrArg Prod.snd he).symm
  rw [hs, hi] at hh
  exact hh

private theorem module_instantiable : Instantiable Lifted.module := by
  intro H
  exact ⟨ready.1, ready.2, ready_instance H⟩

theorem zeroInputRejected_holds : zeroInputRejected := by
  refine ⟨module_instantiable, ?_⟩
  intro H s inst hinst src dst capacity memory
  have hf : (ready.1.withBytes 0 memory).funcs[2]? =
      some (.wasm decoderType allocation.2 Lifted.func2) :=
    (congrArg (fun fs : List FuncInst => fs[2]?)
      (Store.withBytes_funcs ready.1 0 memory)).trans ready_decoder
  have hrdy : CallReturns H (ready.1.withBytes 0 memory) ready.2
      "LZ4_decompress_safe" [.i32 src, .i32 dst, .i32 0, .i32 capacity]
      (fun s' vs => s' = ready.1.withBytes 0 memory ∧ vs = [.i32 4294967295]) := by
    refine ⟨2, ready_export, ?_, empty_run H _ src dst capacity hf⟩
    refine ⟨.wasm decoderType allocation.2 Lifted.func2, hf, ?_⟩
    simp [Val.HasType, FuncInst.type, decoderType]
  have he := instance_unique hinst
  have hs : ready.1 = s := (congrArg Prod.fst he).symm
  have hi : ready.2 = inst := (congrArg Prod.snd he).symm
  rw [hs, hi] at hrdy
  exact hrdy

set_option maxHeartbeats 0 in
theorem regressionCases_holds : regressionCases := by
  refine ⟨module_instantiable, ?_⟩
  intro c hc
  simp only [cases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    apply case_of_computation _ 20000
    unfold computedCase
    decide +kernel

end Proofs
