import FVATest.Subjects.Lz4C.Eval.SegDRest

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
set_option linter.unusedSimpArgs false

theorem d_err (F : Context) (st : Store) (inst : ModuleInst) (src dst n cap cpy j m o' : Nat)
    (mp : BitVec 32) (v16 v18 : Val) (hlo : src ≤ j) (hhi : j ≤ src + n) :
    Err F st inst src dst n cap
      ((ctx1 F).fill ⟨st, ⟨dLs src dst n cap cpy j m o' mp v16 v18, inst⟩,
        (body1.drop 54).map .plain⟩) :=
  ⟨j, hlo, by omega, _, d_const _ _ _ _ _ _ _ _ _ _ _, rfl, rfl⟩

noncomputable def dRestPost (F : Context) (st : Store) (inst : ModuleInst) (mem : MemInst)
    (ma src dst n cap o' m j p : Nat) (c : Config) : Prop :=
  (dst + cap < o' + m + 4 + 5 ∧ Err F st inst src dst n cap c) ∨
  (o' + m + 4 + 5 ≤ dst + cap ∧
    dHeadPost F (st.setMem ma (matchRest mem o' m (dst + cap) (BitVec.ofNat 32 p)))
      inst src dst n cap (o' + m + 4) j c)

theorem d_rest (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (a ma : Nat)
    (mem : MemInst) (src dst n cap o' m j p : Nat) (v16 v18 : Val)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hp0 : dst ≤ p) (hp1 : p ≤ o') (hroom : o' + 8 ≤ dst + cap)
    (hlo : src ≤ j) (hhi : j ≤ src + n) (hlen : m < 2 ^ 31)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size ≤ 2097152) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (dRestPost F st inst mem ma src dst n cap o' m j p)
      ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 v18, inst⟩,
          dAfterPrologue.map .plain⟩) := by
  change Until H _ _ ((ctx1 F).fill
    ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 v18, inst⟩,
      dOuter (dAfterPrologue.map .plain)⟩)
  by_cases hfar : o' + m + 4 + 12 ≤ dst + cap
  · wasm_eval 9 [block_simp, dOuter, d_after_prologue, dNear, dLs, hfar]
    · simp [TraceOK, AccessOK]
    · change Until H _ _ ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 (vI (o' + 8)), inst⟩,
          dAfterNear.map .plain⟩)
      apply (d_far H F st inst a ma mem src dst n cap o' m j p v16
        hcall hfun hm hmem hp0 hp1 hfar hend (by omega)).mono (fun _ hx => hx)
      intro c hc
      exact .inr ⟨by omega, hc⟩
  · by_cases hcap : o' + m + 4 + 5 ≤ dst + cap
    · wasm_eval 12 [block_simp, dOuter, d_after_prologue, dNear, dLs, igtU_ofNat, hfar, hcap]
      · simp [TraceOK, AccessOK]
      · change Until H _ _ ((ctx5 (ctx2 F)).fill
          ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p) v16 (vI (o' + 8)), inst⟩,
            .label 0 [] ((dNear.drop 8).map .plain) :: dAfterNear.map .plain⟩)
        apply (d_near_tail H F st inst a ma mem src dst n cap o' m j p v16
          hcall hfun hm hmem hp0 hp1 hroom hcap hfar hend (by omega)).mono (fun _ hx => hx)
        intro c hc
        exact .inr ⟨hcap, hc⟩
    · wasm_eval 13 [block_simp, dOuter, d_after_prologue, dNear, dLs, igtU_ofNat, hfar, hcap]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        left
        refine ⟨by omega, ?_⟩
        simpa only [BContext.fill, dLs] using
          d_err F st inst src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 p)
            v16 (vI (o' + 8)) hlo hhi

theorem segD : SegD := by
  intro H F st inst ls a ma mem src dst n cap o' off m j hcl h4 h15 h17 h18 h2
    hcall hfun hm hmem hsrc hdst hs hd hsize hsep hj0 hjn hop hroom hoff hm31 ht
  obtain ⟨v3, v16, rfl⟩ := c_decompose hcl h4 h15 h17 h18 h2
  have hM := ofNat32_sub (a := o') (b := off) (by omega) (by omega)
  rw [d_code]
  change Until H _ _ ((ctx1 F).fill
    ⟨st, ⟨cLocals src dst n cap o' off v3 (vI j) m v16, inst⟩, dOuter (dBody.map .plain)⟩)
  by_cases hbad : o' < dst + off
  · wasm_eval 5 [block_simp, dOuter, dBody, cLocals, hbad]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      left
      refine ⟨hbad, ?_⟩
      simpa only [BContext.fill, cLocals, hM] using
        c_err F st inst src dst n cap o' off v3 j m v16 hj0 (by omega)
  · have hmatch : dst + off ≤ o' := by omega
    wasm_eval 9 [block_simp, dOuter, dBody, cLocals, hbad]
    · simp [TraceOK, AccessOK]
    · change Until H _ _ ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap (o' + m + 4) j m o' (BitVec.ofNat 32 (o' - off)) v16
          (vI off), inst⟩,
          .plain dPrologue :: dAfterPrologue.map .plain⟩)
      apply (d_prologue H F st inst a ma mem src dst n cap (o' + m + 4) j m o' off v16
        hcall hfun hm hmem hdst hd hsize hroom hmatch hoff ht).trans
      intro c hc
      obtain ⟨v18, rfl⟩ := hc
      obtain ⟨p, hp, hp0, hp1⟩ := d_prologue_ptr mem dst o' off ht hmatch (by omega)
      simp only [hp]
      apply (d_rest H F (st.setMem ma (prologue mem o' off).1) inst a ma (prologue mem o' off).1
        src dst n cap o' m j p v16 v18 hcall
        (by simpa only [FVA.Wasm.Exec.Ref.setMem_funcs] using hfun) hm (setMem_get hmem _)
        hp0 hp1 hroom hj0 hjn hm31
        (by simpa only [prologue_size] using hd) (by simpa only [prologue_size] using hsize)).mono
        (fun _ hx => hx)
      intro c hc
      rcases hc with ⟨hcap, herr⟩ | ⟨hcap, ls', hhead, heq⟩
      · right; left
        exact ⟨hmatch, hcap, herr⟩
      · right; right
        refine ⟨hmatch, hcap, ls', hhead, ?_⟩
        simpa only [FVA.Wasm.Exec.Ref.setMem_setMem] using heq

#print axioms segD

end Subjects.Lz4C.Eval
