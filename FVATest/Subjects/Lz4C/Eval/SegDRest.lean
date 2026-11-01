import FVATest.Subjects.Lz4C.Eval.SegDLoops

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
set_option linter.unusedSimpArgs false

theorem d_near_tail (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (a ma : Nat)
    (mem : MemInst) (src dst n cap o' m j p : Nat) (v16 : Val)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hp0 : dst ≤ p) (hp1 : p ≤ o') (hroom : o' + 8 ≤ dst + cap)
    (hcap : o' + m + 4 + 5 ≤ dst + cap) (hfar : ¬ o' + m + 4 + 12 ≤ dst + cap)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (dHeadPost F (st.setMem ma (matchRest mem o' m (dst + cap) (BitVec.ofNat 32 p)))
        inst src dst n cap (o' + m + 4) j)
      ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 (vI (o' + 8)), inst⟩,
          .label 0 [] ((dNear.drop 8).map .plain) :: dAfterNear.map .plain⟩) := by
  let q := o' + 8
  let lim := dst + cap - 7
  let e := o' + m + 4
  by_cases hw : q < lim
  · have hk := chunks_spec (q := q) (e := lim) (by omega)
    have hwrite : q + 8 * chunks q lim ≤ dst + cap := by
      rcases hk.2.2 with h1 | hprev
      · rw [h1]; dsimp only [q, lim] at *; omega
      · dsimp only [q, lim] at *; omega
    have hread : p + 8 * chunks q lim ≤ dst + cap := by dsimp only [q] at *; omega
    wasm_eval 9 [block_simp, dNear, dNearSetup, dLs, igeU, hw]
    · simp [TraceOK, AccessOK]
    · let C := Context.label 0 [] ((dNear.drop 9).map .plain)
        (.label 0 [] (dAfterNear.map .plain) (ctx5 (ctx2 F)))
      let ls1 := dLs src dst n cap e j q p (BitVec.ofNat 32 p) v16 (vI q)
      change Until H _ _ (C.fill ⟨st, ⟨ls1, inst⟩,
        [.plain (wcLoop 15 17 10 [])] ++ (dNearSetup.drop 9).map .plain⟩)
      have hwc := wc_until H C st inst ls1 a ma mem 15 17 10 q p lim (chunks q lim) []
        ((dNearSetup.drop 9).map .plain) (by decide) (by decide) (by decide)
        (by rfl) (by rfl) (by rfl) hcall hfun hm hmem (by omega) (by omega) hsize
        hk.1 hk.2.1 hk.2.2
      refine Until.trans (hwc.mono (fun c hc => ?_) (fun _ hx => hx)) ?_
      · refine ⟨fun mm x hx => ?_, fun mm x hx => ?_⟩
        · obtain ⟨rfl, hlo, hhi⟩ := hc.1 mm x hx
          exact ⟨rfl, .inr (.inr ⟨rfl, by omega, by omega⟩)⟩
        · obtain ⟨rfl, hlo, hhi⟩ := hc.2 mm x hx
          exact ⟨rfl, by dsimp only [q] at *; omega, by omega⟩
      · intro c hc
        subst c
        let memW := fwdCopy mem q p (8 * chunks q lim)
        let pp := p + (lim - q)
        have hpp0 : dst ≤ pp := by dsimp only [pp]; omega
        have hpp1 : pp ≤ lim := by dsimp only [pp, q] at *; omega
        change Until H _ _ ((ctx5 (ctx2 F)).fill ⟨_, _,
          .label 0 [] (.label 0 [] (.label 0 [wcLoop 15 17 10 []] [] ::
            (dNearSetup.drop 9).map .plain) :: (dNear.drop 9).map .plain) ::
              dAfterNear.map .plain⟩)
        wasm_eval 10 [block_simp, dNear, dNearSetup, dLs, ls1]
        · simp [TraceOK, AccessOK]
        · change Until H _ _ ((ctx4 (ctx2 F)).fill
            ⟨st.setMem ma memW,
              ⟨dLs src dst n cap e j (q + 8 * chunks q lim) (p + 8 * chunks q lim)
                (BitVec.ofNat 32 pp) v16 (vI lim), inst⟩,
              .label 0 [mainLoop] (.label 0 [] ((dNear.drop 9).map .plain) ::
                dAfterNear.map .plain) :: (body4.drop 1).map .plain⟩)
          have hmodel : matchRest mem o' m (dst + cap) (BitVec.ofNat 32 p) =
              (if lim < e then fwdCopy memW lim pp (e - lim) else memW) := by
            simp only [matchRest, hfar, ite_false, show o' + 8 < dst + cap - 7 from hw,
              ite_true, ofNat32_toNat (show p < 2 ^ 32 by omega), BitVec.ofNat_add_ofNat,
              ofNat32_toNat (show p + (dst + cap - 7 - (o' + 8)) < 2 ^ 32 by omega)]
            rfl
          apply (d_finish_near H F (st.setMem ma memW) inst
            (dLs src dst n cap e j (q + 8 * chunks q lim) (p + 8 * chunks q lim)
              (BitVec.ofNat 32 pp) v16 (vI lim)) ma memW src dst n cap e j pp lim
            (d_const _ _ _ _ _ _ _ _ _ _ _) (by rfl) (by rfl) (by rfl) (by rfl)
            hm (setMem_get hmem _) hpp0 hpp1 (by dsimp only [lim]; omega) (by dsimp only [e]; omega)
            (by simpa only [memW, fwdCopy_size] using hend)
            (by simpa only [memW, fwdCopy_size] using hsize)).mono (fun _ hx => hx)
          intro c hc
          simpa only [dHeadPost, FVA.Wasm.Exec.Ref.setMem_setMem, hmodel] using hc
  · wasm_eval 6 [block_simp, dNear, dNearSetup, dLs, igeU, hw]
    · simp [TraceOK, AccessOK]
    · change Until H _ _ ((ctx4 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap e j m o' (BitVec.ofNat 32 p) v16 (vI q), inst⟩,
          .label 0 [mainLoop] (.label 0 [] ((dNear.drop 9).map .plain) :: dAfterNear.map .plain) ::
            (body4.drop 1).map .plain⟩)
      have hmodel : matchRest mem o' m (dst + cap) (BitVec.ofNat 32 p) =
          (if q < e then fwdCopy mem q p (e - q) else mem) := by
        simp only [matchRest, hfar, ite_false, show ¬ o' + 8 < dst + cap - 7 from hw,
          ofNat32_toNat (show p < 2 ^ 32 by omega)]
        rfl
      apply (d_finish_near H F st inst
        (dLs src dst n cap e j m o' (BitVec.ofNat 32 p) v16 (vI q)) ma mem src dst n cap e j p q
        (d_const _ _ _ _ _ _ _ _ _ _ _) (by rfl) (by rfl) (by rfl) (by rfl)
        hm hmem hp0 (by dsimp only [q]; omega) (by dsimp only [q]; omega)
        (by dsimp only [e]; omega) hend hsize).mono (fun _ hx => hx)
      intro c hc
      simpa only [dHeadPost, hmodel] using hc

theorem d_far (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (a ma : Nat)
    (mem : MemInst) (src dst n cap o' m j p : Nat) (v16 : Val)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hp0 : dst ≤ p) (hp1 : p ≤ o') (hfar : o' + m + 4 + 12 ≤ dst + cap)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (dHeadPost F (st.setMem ma (matchRest mem o' m (dst + cap) (BitVec.ofNat 32 p)))
        inst src dst n cap (o' + m + 4) j)
      ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 (vI (o' + 8)), inst⟩,
          dAfterNear.map .plain⟩) := by
  let ls0 := dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 (vI (o' + 8))
  wasm_eval 2 [block_simp, d_after_near, dLs, ls0]
  · simp [TraceOK, AccessOK]
  · change Until H _ _ ((ctx5 (ctx2 F)).fill
      ⟨st, ⟨ls0, inst⟩,
        vals [vI (o' + 8), vI p, vI 8] ++ [.plain (.call 3)] ++
          (.plain .drop :: dAfterFarCopy.map .plain)⟩)
    apply (d_copy H (ctx5 (ctx2 F)) st inst ls0 a ma mem src dst n cap
      (o' + 8) p 8 (.plain .drop :: dAfterFarCopy.map .plain) hcall hfun hm hmem hend hsize
      ⟨hp0, by omega⟩ ⟨by omega, by omega⟩).trans
    intro c hc
    subst c
    let mem16 := fwdCopy mem (o' + 8) p 8
    by_cases hsmall : m < 13
    · change Until H _ _ ((ctx4 (ctx2 F)).fill ⟨_, _,
        .label 0 [mainLoop] (vals [vI (o' + 8)] ++ (.plain .drop :: dAfterFarCopy.map .plain)) ::
          (body4.drop 1).map .plain⟩)
      rw [main_tail]
      wasm_eval 5 [block_simp, d_after_far_copy, dLs, ls0, hsmall]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        refine ⟨ls0, HeadLocals.of_const (d_const _ _ _ _ _ _ _ _ _ _ _) (by rfl) (by rfl), ?_⟩
        simp only [BContext.fill, matchRest, hfar, ite_true, hsmall,
          ofNat32_toNat (show p < 2 ^ 32 by omega)]
        rfl
    · wasm_eval 10 [block_simp, d_after_far_copy, dLs, ls0, hsmall]
      · simp [TraceOK, AccessOK]
      · let ls1 := dLs src dst n cap (o' + m + 4) j m (o' + 16)
          (BitVec.ofNat 32 (p + 8)) v16 (vI (o' + 8))
        change Until H _ _ ((ctx5 (ctx2 F)).fill
          ⟨st.setMem ma mem16, ⟨ls1, inst⟩, [.plain matchLoop]⟩)
        have hk := chunks_spec (q := o' + 16) (e := o' + m + 4) (by omega)
        have hwrite : o' + 16 + 8 * chunks (o' + 16) (o' + m + 4) ≤ dst + cap := by
          rcases hk.2.2 with h1 | hprev
          · rw [h1]; omega
          · omega
        have hread : p + 8 + 8 * chunks (o' + 16) (o' + m + 4) ≤ dst + cap := by omega
        have hw := s4 (ctx2 F) H (st.setMem ma mem16) inst ls1 a ma mem16
          (o' + 16) (p + 8) (o' + m + 4) (by rfl) (by rfl) (by rfl) hcall
          (by simpa only [FVA.Wasm.Exec.Ref.setMem_funcs] using hfun) hm (setMem_get hmem _)
          (by omega) (by simpa only [mem16, fwdCopy_size] using (show _ ≤ mem.size by omega))
          (by simpa only [mem16, fwdCopy_size] using (show _ ≤ mem.size by omega))
          (by simpa only [mem16, fwdCopy_size] using hsize)
        refine Until.trans (hw.mono (fun c hw' => ?_) (fun _ hx => hx)) ?_
        · refine ⟨fun mm x hx => ?_, fun mm x hx => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hw'.1 mm x hx
            exact ⟨rfl, .inr (.inr ⟨rfl, by omega, by omega⟩)⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hw'.2 mm x hx
            exact ⟨rfl, by omega, by omega⟩
        · intro c hc
          subst c
          apply Until.done
          refine ⟨(ls1.set 17 (vI (o' + 16 + 8 * chunks (o' + 16) (o' + m + 4)))).set 2
            (vI (p + 8 + 8 * chunks (o' + 16) (o' + m + 4))), ?_, ?_⟩
          · apply HeadLocals.of_const
            · exact ((d_const _ _ _ _ _ _ _ _ _ _ _).set (by omega) _).set (by omega) _
            · simp only [List.getElem?_set_ne (by decide : (2 : Nat) ≠ 3),
                List.getElem?_set_ne (by decide : (17 : Nat) ≠ 3)]
              rfl
            · simp only [List.getElem?_set_ne (by decide : (2 : Nat) ≠ 4),
                List.getElem?_set_ne (by decide : (17 : Nat) ≠ 4)]
              rfl
          · simp only [FVA.Wasm.Exec.Ref.setMem_setMem, matchRest, hfar, ite_true, hsmall,
            ite_false,
              ofNat32_toNat (show p < 2 ^ 32 by omega), d_add8,
              ofNat32_toNat (show p + 8 < 2 ^ 32 by omega)]
            rfl

end Subjects.Lz4C.Eval
