import FVA.Impl.Exec.Ref
import FVA.Proof.Numerics.Total
import FVA.Proof.Numerics.Adequacy

/-! # Soundness of value recognition and individual reference steps -/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

theorem toVal_instr (v : Val) : toVal v.instr = some v := by
  cases v with
  | ref r => cases r <;> rfl
  | _ v => simp [Val.instr, toVal, Nat.blt_eq]; exact v.isLt

theorem eq_instr_of_toVal {e : AInstr} {v : Val} (h : toVal e = some v) : e = v.instr := by
  fun_cases toVal e <;> simp_all [toVal, Nat.blt_eq]
  all_goals subst v; simp_all [Val.instr, Nat.mod_eq_of_lt]

theorem implUn_mem {F : FloatFormat} (hF : F.Wide) {z : FVal} (hz : z.WF F)
    (op : FUnOp) : implUn F op z ∈ funop F op z := by
  cases op with
  | abs => exact Set.mem_singleton _
  | neg => exact Set.mem_singleton _
  | sqrt => exact fsqrt_mem hF.1 hz
  | ceil => exact fceil_mem hF hz
  | floor => exact ffloor_mem hF hz
  | trunc => exact ftrunc_mem hF hz
  | nearest => exact fnearest_mem hF hz

theorem implBin_mem {F : FloatFormat} (hF : F.Sane) {a b : FVal}
    (ha : a.WF F) (hb : b.WF F) (op : FBinOp) :
    implBin F op a b ∈ fbinop F op a b := by
  cases op with
  | add => exact fadd_mem hF ha hb
  | sub => exact fsub_mem hF ha hb
  | mul => exact fmul_mem hF ha hb
  | div => exact fdiv_mem hF ha hb
  | min => exact fmin_mem hF ha hb
  | max => exact fmax_mem hF ha hb
  | copysign => exact Set.mem_singleton _

theorem implRel_eq (F : FloatFormat) (op : FRelOp) (a b : FVal) :
    implRel F op a b = frelop F op a b := by
  cases op with
  | eq => exact feq_eq a b
  | ne => exact fne_eq a b
  | lt => exact flt_eq F a b
  | gt => exact fgt_eq F a b
  | le => exact fle_eq F a b
  | ge => exact fge_eq F a b

theorem implTrunc_eq (F : FloatFormat) (N : Nat) (sx : Sx) (z : FVal) :
    implTrunc F N sx z = truncTo F N sx z := by
  cases sx with
  | u => simp only [implTrunc, truncTo, ftruncU_eq]
  | s => simp only [implTrunc, truncTo, ftruncS_eq]

theorem implTruncSat_eq (F : FloatFormat) (N : Nat) (sx : Sx) (z : FVal) :
    implTruncSat F N sx z = truncSatTo F N sx z := by
  cases sx with
  | u => simp only [implTruncSat, truncSatTo, ftruncSatU_eq]
  | s => simp only [implTruncSat, truncSatTo, ftruncSatS_eq]

theorem implConvert_mem {F : FloatFormat} (hF : F.Sane) {M : Nat} (sx : Sx)
    (i : BitVec M) : implConvert F sx i ∈ convertFrom F sx i := by
  cases sx with
  | u => exact fconvertU_mem hF i
  | s => exact fconvertS_mem hF i

/-- The stepper's numeric choice is an allowed result. -/
theorem numStep_mem {i : Instr} {args : List Val} {r : Option Val}
    (h : numStep i args = some r) : r ∈ numResults i args := by
  fun_cases numStep i args <;> simp_all only [numStep, Option.some.injEq, reduceCtorEq]
  all_goals subst r
  all_goals first
    | exact Set.mem_singleton _
    | exact ⟨_, implUn_mem f32fmt_wide (ofBits_wf f32fmt_sane _) _, rfl⟩
    | exact ⟨_, implUn_mem f64fmt_wide (ofBits_wf f64fmt_sane _) _, rfl⟩
    | exact ⟨_, implBin_mem f32fmt_sane (ofBits_wf f32fmt_sane _)
        (ofBits_wf f32fmt_sane _) _, rfl⟩
    | exact ⟨_, implBin_mem f64fmt_sane (ofBits_wf f64fmt_sane _)
        (ofBits_wf f64fmt_sane _) _, rfl⟩
    | exact ⟨_, implConvert_mem f32fmt_sane _ _, rfl⟩
    | exact ⟨_, implConvert_mem f64fmt_sane _ _, rfl⟩
    | exact ⟨_, fdemote_mem (ofBits_wf f64fmt_sane _), rfl⟩
    | exact ⟨_, fpromote_mem (ofBits_wf f32fmt_sane _), rfl⟩
    | simp only [numResults, implRel_eq, implTrunc_eq, implTruncSat_eq,
        Set.mem_singleton_iff]

theorem mem0_eq_some {s : Store} {f : Frame} {a : Nat} {m : MemInst} :
    mem0 s f = some (a, m) ↔ f.inst.mems[0]? = some a ∧ s.mems[a]? = some m := by
  simp only [mem0]
  split <;> simp_all
  grind

theorem tableAt_eq_some {s : Store} {f : Frame} {x a : Nat} {t : TableInst} :
    tableAt s f x = some (a, t) ↔
      f.inst.tables[x]? = some a ∧ s.tables[a]? = some t := by
  simp only [tableAt]
  split <;> simp_all
  grind

theorem callTarget_eq_some {s : Store} {f : Frame} {x y a : Nat} {i : BitVec 32} :
    callTarget s f x y i = some a ↔ CallTarget s f x y i a := by
  fun_cases callTarget s f x y i <;>
    simp_all [CallTarget, tableAt_eq_some]
  all_goals grind

set_option maxHeartbeats 2000000 in
theorem instrStep_sound {H : HostSem} {s s' : Store} {f f' : Frame} {i : Instr}
    {stk stk' : List Val} {out : List AInstr}
    (h : instrStep s f i stk = some (s', f', stk', out)) :
    ∃ args, stk = args.reverse ++ stk' ∧
      Step H ⟨s, f, vals args ++ [.plain i]⟩ ⟨s', f', out⟩ := by
  fun_cases instrStep s f i stk <;>
    simp_all only [instrStep, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Bool.cond_true, Bool.cond_false, Option.some.injEq, Prod.mk.injEq, reduceCtorEq]
  case case1 | case2 | case3 | case4 | case5 | case6 | case7 | case8 =>
    rcases h with ⟨r, hr, rfl, rfl, rfl, rfl⟩
    exact ⟨_, rfl, Step.num (numStep_mem hr)⟩
  case case9 r stk =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨[.ref r], rfl, ?_⟩
    cases hr : r.isNull <;>
      simpa [hr] using (Step.refIsNull (H := H) (s := s) (f := f) (r := r))
  case case10 =>
    rcases h with ⟨a, ha, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.refFunc ha⟩
  case case11 =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[_], rfl, Step.drop⟩
  case case12 ts c v₂ v₁ stk =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨[v₁, v₂, .i32 c], rfl, ?_⟩
    by_cases hc : c = 0 <;>
      simpa [hc] using (Step.select (H := H) (s := s) (f := f) (ts := ts)
        (v₁ := v₁) (v₂ := v₂) (c := c))
  case case13 =>
    rcases h with ⟨v, hv, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.localGet hv⟩
  case case14 x v stk hx =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[_], rfl, Step.localSet (by simpa only [Nat.blt_eq, decide_eq_true_eq] using hx)⟩
  case case16 =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[_], rfl, Step.localTee⟩
  case case17 x a ha =>
    rcases h with ⟨g, hg, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.globalGet ha hg⟩
  case case19 x v stk a ha =>
    rcases h with ⟨g, hg, rfl, rfl, rfl, rfl⟩
    exact ⟨[_], rfl, Step.globalSet ha hg⟩
  case case23 =>
    rcases h with ⟨⟨a, t⟩, ht, rfl, rfl, rfl, rfl⟩
    rcases tableAt_eq_some.mp ht with ⟨ha, ht⟩
    exact ⟨[], rfl, Step.tableSize ha ht⟩
  case case33 x a ha =>
    rcases h with ⟨e, he, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.elemDrop ha he⟩
  case case43 =>
    rcases h with ⟨⟨a, mem⟩, hm, rfl, rfl, rfl, rfl⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    exact ⟨[], rfl, Step.memorySize ha hm⟩
  case case49 x a ha =>
    rcases h with ⟨di, hdi, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.dataDrop ha hdi⟩
  case case51 =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.nop⟩
  case case52 =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.unreachable⟩
  case case55 bt thn els c stk =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨[.i32 c], rfl, ?_⟩
    by_cases hc : c = 0
    · subst c; simpa using (Step.ifFalse (H := H) (s := s) (f := f)
        (bt := bt) (thn := thn) (els := els))
    · have hb : (c == 0) = false := beq_eq_false_iff_ne.mpr hc
      rw [hb]
      exact Step.ifTrue hc
  case case56 l c stk =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨[.i32 c], rfl, ?_⟩
    by_cases hc : c = 0
    · subst c; simpa using (Step.brIfFalse (H := H) (s := s) (f := f) (l := l))
    · have hb : (c == 0) = false := beq_eq_false_iff_ne.mpr hc
      rw [hb]
      exact Step.brIfTrue hc
  case case57 =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨[_], rfl, Step.brTable⟩
  case case58 =>
    rcases h with ⟨a, ha, rfl, rfl, rfl, rfl⟩
    exact ⟨[], rfl, Step.call ha⟩
  case case59 x y i stk =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨[.i32 i], rfl, ?_⟩
    cases ht : callTarget s f x y i with
    | some a => exact Step.callIndirect (callTarget_eq_some.mp ht)
    | none =>
      apply Step.callIndirectTrap
      intro a ha
      have := callTarget_eq_some.mpr ha
      simp only [ht, reduceCtorEq] at this
  case case21 x i stk =>
    rcases h with ⟨⟨a, t⟩, ht, h⟩
    rcases tableAt_eq_some.mp ht with ⟨ha, ht⟩
    cases hr : t.elem[i.toNat]? <;> simp only [hr, Prod.mk.injEq] at h
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_], rfl, Step.tableGetTrap ha ht (by simpa using hr)⟩
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_], rfl, Step.tableGet ha ht hr⟩
  case case22 x r i stk =>
    rcases h with ⟨⟨a, t⟩, ht, h⟩
    rcases tableAt_eq_some.mp ht with ⟨ha, ht⟩
    cases hb : Nat.blt i.toNat t.elem.length <;>
      simp only [hb, Bool.cond_true, Bool.cond_false, Prod.mk.injEq] at h
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_, _], rfl, Step.tableSetTrap ha ht (nblt_false.mp hb)⟩
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_, _], rfl, Step.tableSet ha ht (nblt_true.mp hb)⟩
  case case24 x n r stk =>
    rcases h with ⟨⟨a, t⟩, ht, h⟩
    rcases tableAt_eq_some.mp ht with ⟨ha, ht⟩
    cases hg : t.grow n.toNat r <;> simp only [hg, Prod.mk.injEq] at h
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_, _], rfl, Step.tableGrowFail⟩
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_, _], rfl, Step.tableGrow ha ht hg⟩
  case case25 x n r i stk =>
    rcases h with ⟨⟨a, t⟩, ht, h⟩
    rcases tableAt_eq_some.mp ht with ⟨ha, ht⟩
    simp only [cond] at h
    split at h
    · rename_i hb
      rcases Prod.mk.inj h with ⟨rfl, h⟩
      rcases h with ⟨⟩
      exact ⟨[_, _, _], rfl, Step.tableFillTrap ha ht (nblt_true.mp hb)⟩
    · rename_i hb
      have hb := nblt_false.mp hb
      split at h
      · rename_i hz
        have hn : n = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa using Nat.beq_eq.mp hz
        subst n
        cases h
        exact ⟨[_, _, _], rfl, Step.tableFillZero ha ht (by simpa using hb)⟩
      · rename_i hn
        cases h
        have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
          simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
        exact ⟨[_, _, _], rfl, Step.tableFill ha ht hn hb⟩
  case case26 x y n src dst stk tx Tx ty Ty hty htx hb =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases tableAt_eq_some.mp htx with ⟨hx, hTx⟩
    rcases tableAt_eq_some.mp hty with ⟨hy, hTy⟩
    refine ⟨[_, _, _], rfl, Step.tableCopyTrap hx hy ?_⟩
    simp only [Bool.or_eq_true, nblt_true] at hb
    exact hb.elim (fun h => Or.inl ⟨Ty, hTy, h⟩) (fun h => Or.inr ⟨Tx, hTx, h⟩)
  case case27 x y n src dst stk tx Tx ty Ty hty htx hb hz =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases tableAt_eq_some.mp htx with ⟨hx, hTx⟩
    rcases tableAt_eq_some.mp hty with ⟨hy, hTy⟩
    have hn : n = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa using Nat.beq_eq.mp hz
    subst n
    simp only [Bool.or_eq_false_iff, nblt_false] at hb
    exact ⟨[_, _, _], rfl, Step.tableCopyZero hx hy hTx hTy hb.1 hb.2⟩
  case case28 x y n src dst stk tx Tx ty Ty hty htx hb hn hdir =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases tableAt_eq_some.mp htx with ⟨hx, hTx⟩
    rcases tableAt_eq_some.mp hty with ⟨hy, hTy⟩
    simp only [Bool.or_eq_false_iff, nblt_false] at hb
    have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
      simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
    exact ⟨[_, _, _], rfl, Step.tableCopyUp hx hy hTx hTy hn hb.1 hb.2
      (by simpa only [Nat.ble_eq, decide_eq_true_eq] using hdir)⟩
  case case29 x y n src dst stk tx Tx ty Ty hty htx hb hn hdir =>
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases tableAt_eq_some.mp htx with ⟨hx, hTx⟩
    rcases tableAt_eq_some.mp hty with ⟨hy, hTy⟩
    simp only [Bool.or_eq_false_iff, nblt_false] at hb
    have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
      simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
    exact ⟨[_, _, _], rfl, Step.tableCopyDown hx hy hTx hTy hn hb.1 hb.2
      (by simpa only [← Bool.not_eq_true, Nat.ble_eq, Nat.not_le] using hdir)⟩
  case case31 x y n src dst stk tx t ea hea htx =>
    rcases h with ⟨e, he, h⟩
    rcases tableAt_eq_some.mp htx with ⟨hx, ht⟩
    simp only [cond] at h
    split at h
    · rename_i hb
      cases h
      refine ⟨[_, _, _], rfl, Step.tableInitTrap hx hea ?_⟩
      simp only [Bool.or_eq_true, nblt_true] at hb
      exact hb.elim (fun h => Or.inl ⟨e, he, h⟩) (fun h => Or.inr ⟨t, ht, h⟩)
    · rename_i hb
      simp only [Bool.or_eq_false_iff, nblt_false] at hb
      split at h
      · rename_i hz
        have hn : n = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa using Nat.beq_eq.mp hz
        subst n
        cases h
        exact ⟨[_, _, _], rfl, Step.tableInitZero hx hea ht he hb.1 hb.2⟩
      · rename_i hn
        have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
      simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
        split at h
        · rename_i r hr
          cases h
          exact ⟨[_, _, _], rfl, Step.tableInit hx hea ht he hn hb.1 hb.2 hr⟩
        · rename_i hr
          have hbad : e.elem.length ≤ src.toNat := by simpa using hr
          omega
  case case35 t m i stk =>
    rcases h with ⟨⟨a, mem⟩, hm, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    simp only [cond] at h
    split at h <;> rename_i hb <;> cases h
    · exact ⟨[_], rfl, Step.loadTrap ha hm (nblt_true.mp hb)⟩
    · exact ⟨[_], rfl, Step.load ha hm (nblt_false.mp hb)⟩
  case case36 w p sx m i stk =>
    rcases h with ⟨⟨a, mem⟩, hm, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    simp only [cond] at h
    split at h <;> rename_i hb <;> cases h
    · exact ⟨[_], rfl, Step.loadPackedTrap ha hm (nblt_true.mp hb)⟩
    · exact ⟨[_], rfl, Step.loadPacked ha hm (nblt_false.mp hb)⟩
  case case37 t m v i stk a mem c hv hm ea hb =>
    dsimp only [ea] at hb
    simp only [hb, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    exact ⟨[_, _], rfl, Step.storeTrap ha hm hv (nblt_true.mp hb)⟩
  case case38 t m v i stk a mem c hv hm ea hb =>
    dsimp only [ea] at hb
    simp only [hb, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    exact ⟨[_, _], rfl, Step.store ha hm hv (nblt_false.mp hb)⟩
  case case40 w p m v i stk a mem c hv hm ea hb =>
    dsimp only [ea] at hb
    simp only [hb, Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    exact ⟨[_, _], rfl, Step.storePackedTrap ha hm hv (nblt_true.mp hb)⟩
  case case41 w p m v i stk a mem c hv hm ea hb =>
    dsimp only [ea] at hb
    simp only [hb, Bool.cond_false, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    exact ⟨[_, _], rfl, Step.storePacked ha hm hv (nblt_false.mp hb)⟩
  case case44 n stk =>
    rcases h with ⟨⟨a, mem⟩, hm, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    cases hg : mem.grow n.toNat <;> simp only [hg, Prod.mk.injEq] at h
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_], rfl, Step.memoryGrowFail⟩
    · rcases h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨[_], rfl, Step.memoryGrow ha hm hg⟩
  case case45 n v d stk =>
    rcases h with ⟨⟨a, mem⟩, hm, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    simp only [cond] at h
    split at h
    · rename_i hb
      cases h
      exact ⟨[_, _, _], rfl, Step.memoryFillTrap ha hm (nblt_true.mp hb)⟩
    · rename_i hb
      have hb := nblt_false.mp hb
      split at h
      · rename_i hz
        have hn : n = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa using Nat.beq_eq.mp hz
        subst n
        cases h
        exact ⟨[_, _, _], rfl, Step.memoryFillZero ha hm (by simpa using hb)⟩
      · rename_i hn
        cases h
        have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
          simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
        exact ⟨[_, _, _], rfl, Step.memoryFill ha hm hn hb⟩
  case case46 n src dst stk =>
    rcases h with ⟨⟨a, mem⟩, hm, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    simp only [cond] at h
    split at h
    · rename_i hb
      cases h
      exact ⟨[_, _, _], rfl, Step.memoryCopyTrap ha hm (by
        simpa only [Bool.or_eq_true, nblt_true] using hb)⟩
    · rename_i hb
      simp only [Bool.or_eq_false_iff, nblt_false] at hb
      split at h
      · rename_i hz
        have hn : n = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa using Nat.beq_eq.mp hz
        subst n
        cases h
        exact ⟨[_, _, _], rfl, Step.memoryCopyZero ha hm hb.1 hb.2⟩
      · rename_i hn
        have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
      simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
        split at h <;> rename_i hdir <;> cases h
        · exact ⟨[_, _, _], rfl, Step.memoryCopyUp ha hm hn hb.1 hb.2
            (by simpa only [Nat.ble_eq, decide_eq_true_eq] using hdir)⟩
        · exact ⟨[_, _, _], rfl, Step.memoryCopyDown ha hm hn hb.1 hb.2
            (by simpa only [← Bool.not_eq_true, Nat.ble_eq, Nat.not_le] using hdir)⟩
  case case47 x n src dst stk a mem da hda hm =>
    rcases h with ⟨di, hdi, h⟩
    rcases mem0_eq_some.mp hm with ⟨ha, hm⟩
    simp only [cond] at h
    split at h
    · rename_i hb
      cases h
      refine ⟨[_, _, _], rfl, Step.memoryInitTrap ha hda hm ?_⟩
      simp only [Bool.or_eq_true, nblt_true] at hb
      exact hb.elim (fun h => Or.inl ⟨di, hdi, h⟩) Or.inr
    · rename_i hb
      simp only [Bool.or_eq_false_iff, nblt_false] at hb
      split at h
      · rename_i hz
        have hn : n = 0 := by
          apply BitVec.eq_of_toNat_eq
          simpa using Nat.beq_eq.mp hz
        subst n
        cases h
        exact ⟨[_, _, _], rfl, Step.memoryInitZero ha hda hm hdi hb.1 hb.2⟩
      · rename_i hn
        have hn : 0 < n.toNat := Nat.pos_of_ne_zero (by
      simpa only [← Bool.not_eq_true, Nat.beq_eq] using hn)
        split at h
        · rename_i b hbyte
          cases h
          exact ⟨[_, _, _], rfl, Step.memoryInit ha hda hm hdi hn hb.1 hb.2 hbyte⟩
        · rename_i hbyte
          have hbad : di.data.length ≤ src.toNat := by simpa using hbyte
          omega
  case case53 bt body =>
    rcases h with ⟨ft, hft, h⟩
    simp only [cond] at h
    split at h
    · contradiction
    · rename_i hb
      cases h
      refine ⟨(stk.take ft.params.length).reverse, ?_, Step.block hft ?_⟩
      · simp
      · simp [Nat.min_eq_left (nblt_false.mp hb)]
  case case54 bt body =>
    rcases h with ⟨ft, hft, h⟩
    simp only [cond] at h
    split at h
    · contradiction
    · rename_i hb
      cases h
      refine ⟨(stk.take ft.params.length).reverse, ?_, Step.loop hft ?_⟩
      · simp
      · simp [Nat.min_eq_left (nblt_false.mp hb)]

end FVA.Wasm.Exec.Ref
