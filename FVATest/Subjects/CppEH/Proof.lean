import FVATest.Subjects.CppEH.Twin
import FVA.Proof.Valid.Validator
import FVA.Proof.Exec.Imports
import FVA.Proof.Lib.Witness
import FVA.Proof.Wasi.WfRun

/-! Proof of `r1` (contract U28g F3): the odd chain (`oddCore` over the odd twin, input 1) and the
even chain (twin 0) carry `SysMust` from each input's final state back to the launch state;
`launch_sysMust` carries it to every launch. -/

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Machine FVA.Wasm.Exec.Machine.Oblivious FVA.Wasi
  FVA.Wasm.Num

set_option maxRecDepth 100000

namespace Subjects.CppEH

theorem odd {Q : SysOutcome State → Prop} (x : BitVec 32) (hx : x.toNat % 2 = 1)
    (hQ : ∀ σ (s : Store), s.exns.length = 1 →
      Q (.returned σ s [.i32 (ixor x (BitVec.ofNat 32 2779096485))])) :
    SysMust Wd true Q (start, (MState.ofInvoke inst.1 133 [.i32 x]).abs) := by
  have hI := instF
  simp only [Prod.mk.injEq] at hI
  obtain ⟨hfW, htW, hdW, hbW, hiW, hfE, htE, hdE⟩ := hI
  have t11 := tw11 1 (.inl rfl)
  simp only [Prod.mk.injEq] at t11
  obtain ⟨hσ11, hb11, hc11, hs11, hl11⟩ := t11
  have t1233 := tw1233
  simp only [Prod.mk.injEq, decide_eq_true_eq] at t1233
  obtain ⟨hσ1233, hb1233, hc1233, hs1233, hl1233, hI1233, hm1233, hz1233⟩ := t1233
  have t3264 := tw3264
  simp only [Prod.mk.injEq, decide_eq_true_eq] at t3264
  obtain ⟨he3264, hb3264, hc3264, hs3264, hl3264, hI3264, hm3264, hz3264, hr3264⟩ := t3264
  have t3526 := tw3526
  simp only [Prod.mk.injEq, decide_eq_true_eq] at t3526
  obtain ⟨he3526, hb3526, hc3526, hs3526, hl3526, hm3526, hz3526⟩ := t3526
  have t3533 := tw3533
  simp only [Prod.mk.injEq, decide_eq_true_eq] at t3533
  obtain ⟨he3533, hb3533, hc3533, hs3533, hl3533, hk3533, hiW3533, hf3533, ht3533, hd3533, hm3533,
    hz3533⟩ := t3533
  have t3741 := tw3741
  simp only [Prod.mk.injEq, decide_eq_true_eq] at t3741
  obtain ⟨he3741, hb3741, hc3741, hs3741, hk3741, hm3741, hz3741, hn3741⟩ := t3741
  -- the twin's cut equations
  have r11 := run_cut hσ11 hb11
  have r1233 := run_cut hσ1233 hb1233
  have r3264 := run_cut rfl hb3264
  have r3526 := run_cut rfl hb3526
  have r3533 := run_cut rfl hb3533
  have r3741 := run_cut rfl hb3741
  -- the twin's seams fix the twin at each seam's end
  have e5 := twinEnd (a := 0) (b := 5) (x0 := 1) rfl
    (runG1 (X := Xh) start_exited hfW htW hdW hbW hiW hfE htE hdE)
  have e15 := twinEnd r11
    (runG2 (X := Xh) start_exited hc11 hs11 hl11 (r := iand 1 (BitVec.ofNat 32 1)) rfl)
  have e1236 := twinEnd r1233
    (runG3 (X := Xh) start_exited hc1233 hs1233 hl1233 hI1233 hm1233 hz1233)
  have e3266 := twinEnd r3264
    (runG4 (X := Xh) he3264 hc3264 hs3264 hl3264 hI3264 hm3264 hz3264 hr3264)
  have e3532 := twinEnd r3526 (runG5 (X := Xh) he3526 (by norm_num) hc3526 hs3526 hl3526
    (r := ixor 1 (BitVec.ofNat 32 2779096485)) rfl)
  have e3538 := twinEnd r3533
    (runG6 (X := Xh) he3533 hc3533 hs3533 hl3533 hk3533 hiW3533 hf3533 ht3533 hd3533)
  exact oddCore x hx hQ hfW htW hdW hbW hiW hfE htE hdE inst_inv
    e5.1 cert5 ((run_add 6 e5.2.1).symm.trans r11)
    hc11 hs11 hl11 e15.1 cert15 ((run_add 1218 e15.2.1).symm.trans r1233)
    hc1233 hs1233 hl1233 hI1233 hm1233 hz1233 e1236.1 cert1236
    ((run_add 2028 e1236.2.1).symm.trans r3264)
    he3264 hc3264 hs3264 hl3264 hI3264 hm3264 hz3264 hr3264 e3266.1 cert3266
    ((run_add 260 e3266.2.1).symm.trans r3526)
    he3526 hc3526 hs3526 hl3526 hm3526 hz3526 e3532.1 cert3532
    ((run_add 1 e3532.2.1).symm.trans r3533)
    he3533 hc3533 hs3533 hl3533 hk3533 hiW3533 hf3533 ht3533 hd3533 hm3533 hz3533 e3538.1 cert3538
    ((run_add 203 e3538.2.1).symm.trans r3741)
    he3741 hc3741 hs3741 hk3741 hm3741 hz3741 hn3741


theorem even {Q : SysOutcome State → Prop} (x : BitVec 32) (hx : x.toNat % 2 = 0)
    (hQ : ∀ σ (s : Store), s.exns.length = 0 →
      Q (.returned σ s [.i32 (ior x (BitVec.ofNat 32 1))])) :
    SysMust Wd true Q (start, (MState.ofInvoke inst.1 133 [.i32 x]).abs) := by
  have hI := instF
  simp only [Prod.mk.injEq] at hI
  obtain ⟨hfW, htW, hdW, hbW, hiW, hfE, htE, hdE⟩ := hI
  -- S1a
  have e5 := twinEnd (a := 0) (b := 5) (x0 := 0) rfl
    (runG1 (X := Xh) start_exited hfW htW hdW hbW hiW hfE htE hdE)
  refine linkG1 x 0 hfW htW hdW hbW hiW hfE htE hdE inst_inv e5.1 ?_
  -- F0′
  have t11 := tw11 0 (.inr rfl)
  simp only [Prod.mk.injEq] at t11
  obtain ⟨hσ11, hb11, hc11, hs11, hl11⟩ := t11
  refine linkF (a := 5) (n := 6) cert5e (valsOK_vv x x) (by simp [BytesOK, ride, ps1, vv])
    e5.2.1 (run_cut hσ11 hb11) ?_
  -- S1c′
  have e15 := twinEnd (run_cut hσ11 hb11)
    (runG2 (X := Xh) start_exited hc11 hs11 hl11 (r := iand 0 (BitVec.ofNat 32 1)) rfl)
  refine linkG2 x 0 (by simp [hx]) hc11 hs11 hl11 (run_inv 11 0) e15.1 ?_
  -- F15′
  have t20 := tw20
  simp only [Prod.mk.injEq] at t20
  obtain ⟨hσ20, hb20, hc20, hs20, hl20⟩ := t20
  refine linkF (a := 15) (n := 5) cert15e (valsOK_vv x x) (by simp [BytesOK, ride, ps1, vv])
    e15.2.1 (run_cut hσ20 hb20) ?_
  -- S4′a
  have e26 := twinEnd (run_cut hσ20 hb20)
    (runG5 (X := Xh) start_exited (by norm_num) hc20 hs20 hl20
      (r := ior 0 (BitVec.ofNat 32 1)) rfl)
  rw [show ride ps1 (vv x x) = ride ps1 (vv x x) ++ [] from (List.append_nil _).symm]
  refine linkG5 x 0 (by norm_num) (r := ior x (BitVec.ofNat 32 1)) rfl rfl byteOnly_nil
    start_exited hc20 hs20 hl20 (run_inv 20 0) (by simp [BytesOK]) e26.1 ?_
  rw [List.append_nil]
  -- F26′
  have t27 := tw27
  simp only [Prod.mk.injEq] at t27
  obtain ⟨hσ27, hb27, hc27, hs27, hl27, hk27, hiW27, hf27, ht27, hd27⟩ := t27
  refine linkF (a := 26) (n := 1) cert26e (valsOK_vv _ x) (by simp [BytesOK, ride, ps1, vv])
    e26.2.1 (run_cut hσ27 hb27) ?_
  -- S4′b
  have e32 := twinEnd (run_cut hσ27 hb27)
    (runG6 (X := Xh) start_exited hc27 hs27 hl27 hk27 hiW27 hf27 ht27 hd27)
  rw [show ride ps1 (vv (ior x (BitVec.ofNat 32 1)) x) =
    ride ps1 (vv (ior x (BitVec.ofNat 32 1)) x) ++ [] from (List.append_nil _).symm]
  refine linkG6 x 0 _ _ byteOnly_nil start_exited hc27 hs27 hl27 hk27 hiW27 hf27 ht27 hd27
    (run_inv 27 0) (by simp [BytesOK]) e32.1 ?_
  rw [List.append_nil]
  -- F1d′
  have t235 := tw235
  simp only [Prod.mk.injEq] at t235
  obtain ⟨hσ235, hb235, hc235, hs235, hk235, hn235⟩ := t235
  refine linkF (a := 32) (n := 203) cert32e (valsOK_vv x _) (by simp [BytesOK, ride, ps2, vv])
    e32.2.1 (run_cut hσ235 hb235) ?_
  -- S6′
  rw [show ride ps2 (vv x (ior x (BitVec.ofNat 32 1))) =
    ride ps2 (vv x (ior x (BitVec.ofNat 32 1))) ++ [] from (List.append_nil _).symm]
  exact linkG7 x _ byteOnly_nil start_exited hc235 hs235 hk235 (run_inv 235 0) (by simp [BytesOK])
    (fun s hs => hQ _ s (by rw [hs]; exact hn235))


/-- An even input's successor = setting its low bit. -/
theorem ior_one_of_even {x : BitVec 32} (h : x.toNat % 2 = 0) :
    ior x (BitVec.ofNat 32 1) = x + 1 := by
  have h0 : x &&& 1#32 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.and_one_is_mod, h]
  exact (BitVec.add_eq_or_of_and_eq_zero x 1#32 h0).symm

/-! ## Launch -/

theorem eh_export : inst.2.exportFunc "eh" = some 133 := by decide +kernel

theorem memory_export : inst.2.exportMem "memory" = some 0 := by decide +kernel

theorem valid : Valid.ModuleValid md := Valid.validate_sound (by decide +kernel)

theorem invokeOK (x : BitVec 32) : InvokeOK inst.1.abs 133 [.i32 x] := by
  have hI := instF
  simp only [Prod.mk.injEq] at hI
  obtain ⟨hfW, htW, -, -, -, -, -, -⟩ := hI
  exact ⟨_, _, hfW, htW, .cons trivial .nil⟩

theorem launches (x : BitVec 32) : ∃ c mem, Launch md "eh" [.i32 x] c mem := by
  have hm : ImportsMatch (hostStore md) md (hostImports md) :=
    (Ref.importsMatch_iff _ _ _).mp (by decide +kernel)
  refine ⟨_, _, launch_of_instantiateU inst_eq valid (by decide +kernel) (by decide +kernel) ?_ ?_
    hm eh_export memory_export (invokeOK x)⟩
  · intro im h
    have hall : md.imports.all (fun im => match im.desc with
        | .func _ => true
        | _ => false) = true := by decide +kernel
    have him := List.all_eq_true.mp hall im h
    cases hd : im.desc <;> simp_all
  · intro id im h _ _
    have : ∀ id < md.imports.length, (bind md id).isSome = true := by decide +kernel
    exact this id (List.getElem?_eq_some_iff.mp h).1

/-- The fixed process start is a well-formed WASI state (contract U28g Claim, U29a T7). -/
theorem start_wf : start.Wf := by decide

/-- The claim. -/
theorem r1_proof : r1 := by
  intro x
  refine ⟨launches x, fun c mem hl => ?_⟩
  refine launch_sysMust inst_eq eh_export memory_export (n := 0) (σ := start) rfl ?_ c mem hl
  by_cases hx : x.toNat % 2 = 0
  · exact even x hx (fun σ s _ => ⟨σ, s, by
      simp only [hx, ↓reduceIte]
      exact congrArg (fun v => SysOutcome.returned σ s [Val.i32 v]) (ior_one_of_even hx)⟩)
  · exact odd x (by omega) (fun σ s _ => ⟨σ, s, by simp only [hx, ↓reduceIte]; rfl⟩)

/-- Path evidence (contract U28g F3; outside `r1`, never reviewed): from `start`, every launch on
an odd input ends with exactly one exception instance in its store (`eh` throws `x` and catches
it), on an even input with none. -/
theorem eh_path (x : BitVec 32) : ∀ c mem, Launch Lifted.module "eh" [.i32 x] c mem →
    SysMust ((world Lifted.module mem).restrict (E Lifted.module mem)) true
      (fun o => ∃ (τ : State) (s : Store) (vs : List Val), o = .returned τ s vs ∧
        s.exns.length = if x.toNat % 2 = 0 then 0 else 1) (start, c) := by
  intro c mem hl
  refine launch_sysMust inst_eq eh_export memory_export (n := 0) (σ := start) rfl ?_ c mem hl
  by_cases hx : x.toNat % 2 = 0
  · exact even x hx (fun σ s h => ⟨σ, s, _, rfl, by simp only [hx, ↓reduceIte]; exact h⟩)
  · exact odd x (by omega) (fun σ s h => ⟨σ, s, _, rfl, by simp only [hx, ↓reduceIte]; exact h⟩)

/-- The domain is inhabited (U37): input 0 and its launch. -/
@[fva_witness r1] theorem r1_domain : fva_obligation% r1 := ⟨⟨0, trivial⟩, 0, launches 0⟩

end Subjects.CppEH
