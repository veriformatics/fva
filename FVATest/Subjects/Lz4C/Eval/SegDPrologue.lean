import FVATest.Subjects.Lz4C.Eval.SegDCommon

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
set_option linter.unusedSimpArgs false

noncomputable def dProloguePost (F : Context) (st : Store) (inst : ModuleInst) (mem : MemInst)
    (ma src dst n cap cpy j m o' off : Nat) (v16 : Val) (c : Config) : Prop :=
  ∃ v18, c = (ctx5 (ctx2 F)).fill
    ⟨st.setMem ma (prologue mem o' off).1,
      ⟨dLs src dst n cap cpy j m o' (prologue mem o' off).2 v16 v18, inst⟩,
      dAfterPrologue.map .plain⟩

theorem d_prologue (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst) (a ma : Nat)
    (mem : MemInst) (src dst n cap cpy j m o' off : Nat) (v16 : Val)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hdst : 131072 ≤ dst) (hend : dst + cap ≤ mem.size) (hsize : mem.size ≤ 2097152)
    (hroom : o' + 8 ≤ dst + cap) (hmatch : dst + off ≤ o') (hoff : off < 65536)
    (ht : TablesOK mem) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (dProloguePost F st inst mem ma src dst n cap cpy j m o' off v16)
      ((ctx5 (ctx2 F)).fill
        ⟨st, ⟨dLs src dst n cap cpy j m o' (BitVec.ofNat 32 (o' - off)) v16 (vI off), inst⟩,
          .plain dPrologue :: dAfterPrologue.map .plain⟩) := by
  have hmp0 : dst ≤ o' - off := by omega
  have hmp1 : o' - off ≤ o' := by omega
  have hM := ofNat32_sub (a := o') (b := off) (by omega) (by omega)
  by_cases hbig : 7 < off
  · have hpro : prologue mem o' off =
        (fwdCopy mem o' (o' - off) 8, BitVec.ofNat 32 (o' - off + 8)) := by
      simp only [prologue, hbig, ite_true, hM,
        ofNat32_toNat (show o' - off < 2 ^ 32 by omega), d_add8]
    wasm_eval 8 [block_simp, dPrologue, dSmall, dLarge, dLs, igtU_ofNat, hbig]
    · simp [TraceOK, AccessOK]
    · let C := Context.label 0 [] (dAfterPrologue.map .plain) (ctx5 (ctx2 F))
      change Until H _ _ (C.fill
        ⟨st, ⟨dLs src dst n cap cpy j m o' (BitVec.ofNat 32 (o' - off)) v16 (vI off), inst⟩,
          vals [vI o', vI (o' - off), vI 8] ++ [.plain (.call 3)] ++ (dLarge.drop 4).map .plain⟩)
      apply (d_copy H C st inst
        (dLs src dst n cap cpy j m o' (BitVec.ofNat 32 (o' - off)) v16 (vI off))
        a ma mem src dst n cap o' (o' - off) 8 ((dLarge.drop 4).map .plain)
        hcall hfun hm hmem hend (by omega) ⟨hmp0, by omega⟩ ⟨by omega, hroom⟩).trans
      intro c hc
      subst c
      change Until H _ _ ((ctx5 (ctx2 F)).fill ⟨_, _,
        .label 0 [] (vals [vI o'] ++ (dLarge.drop 4).map .plain) :: dAfterPrologue.map .plain⟩)
      wasm_eval 5 [block_simp, dLarge, dLs]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        refine ⟨vI off, ?_⟩
        simp only [hpro, dLs, BContext.fill]
  · have hsmall : off < 8 := by omega
    have hr0 : ¬ mem.size < o' - off + 1 := by omega
    have hr1 : ¬ mem.size < o' - off + 1 + 1 := by omega
    have hr2 : ¬ mem.size < o' - off + 2 + 1 := by omega
    have hr3 : ¬ mem.size < o' - off + 3 + 1 := by omega
    have hw0 : ¬ mem.size < o' + 1 := by omega
    have hw1 : ¬ mem.size < o' + 1 + 1 := by omega
    have hw2 : ¬ mem.size < o' + 2 + 1 := by omega
    have hw3 : ¬ mem.size < o' + 3 + 1 := by omega
    wasm_eval 23 [block_simp, dPrologue, dSmall, dLarge, dLs, igtU_ofNat, hbig, hm, hmem,
      Val.numBits, hr0, hr1, hr2, hr3, hw0, hw1, hw2, hw3]
    · simp [TraceOK, AccessOK, ReadSet, Span]
      repeat' constructor
      all_goals intro x hx0 hx1
      all_goals first | (constructor <;> omega) | (right; right; constructor <;> omega)
    · let p0 := o' - off
      let inc := inc32[off]!
      let dec := dec64[off]!
      let p := p0 + inc
      let next := p0 + dDelta off
      let m4 := fwdCopy (mem.write o' 4 0) o' p0 4
      have hb := d_table_bounds hsmall
      have hp0 : dst ≤ p := by dsimp only [p, p0]; omega
      have hp1 : p ≤ o' := by dsimp only [p, p0, inc]; omega
      have ht4 : TablesOK m4 := d_tables_copy (d_tables_zero ht (by omega)) (by omega)
      have hreadInc : m4.read (4 * off + 65536) 4 = inc := by
        rw [show 4 * off + 65536 = 65536 + 4 * off by omega]
        exact (ht4 off hsmall).1
      have hsh : ishl (BitVec.ofNat 32 off) (BitVec.ofNat 32 2) = BitVec.ofNat 32 (4 * off) := by
        simp only [ishl, ofNat32_toNat (show off < 2 ^ 32 by omega),
          ofNat32_toNat (show 2 < 2 ^ 32 by decide), Nat.reduceMod, Nat.reducePow]
        rw [Nat.mul_comm]
      change Until H _ _ ((ctx5 (ctx2 F)).fill
        ⟨st.setMem ma m4, ⟨dLs src dst n cap cpy j m o' (BitVec.ofNat 32 p0) v16 (vI off), inst⟩,
          .label 0 [] (.label 0 [] ((dSmall.drop 23).map .plain) :: dLarge.map .plain) ::
            dAfterPrologue.map .plain⟩)
      have hs4 : m4.size = mem.size := by simp only [m4, fwdCopy_size, write_size]
      wasm_eval 11 [block_simp, dSmall, dLs, hm, hmem, hs4, hsh, hreadInc]
      · simp [TraceOK, AccessOK, ReadSet, Span]
        intro x hx0 hx1
        left
        omega
      · let C := Context.label 0 [] (dLarge.map .plain)
          (.label 0 [] (dAfterPrologue.map .plain) (ctx5 (ctx2 F)))
        change Until H _ _ (C.fill
          ⟨st.setMem ma m4,
            ⟨dLs src dst n cap cpy j m o' (BitVec.ofNat 32 p) v16 (vI (4 * off)), inst⟩,
            vals [vI (o' + 4), vI p, vI 4] ++ [.plain (.call 3)] ++ (dSmall.drop 36).map .plain⟩)
        apply (d_copy H C (st.setMem ma m4) inst
          (dLs src dst n cap cpy j m o' (BitVec.ofNat 32 p) v16 (vI (4 * off)))
          a ma m4 src dst n cap (o' + 4) p 4 ((dSmall.drop 36).map .plain) hcall
          (by simpa only [FVA.Wasm.Exec.Ref.setMem_funcs] using hfun) hm (setMem_get hmem _)
          (by simpa only [hs4] using hend) (by rw [hs4]; omega)
          ⟨hp0, by omega⟩ ⟨by omega, by omega⟩).trans
        intro c hc
        subst c
        let m8 := fwdCopy m4 (o' + 4) p 4
        have ht8 : TablesOK m8 := d_tables_copy ht4 (by omega)
        have hreadDec : m8.read (4 * off + 65568) 4 = dec := by
          rw [show 4 * off + 65568 = 65568 + 4 * off by omega]
          exact (ht8 off hsmall).2
        have hnext : BitVec.ofNat 32 p - BitVec.ofNat 32 dec = BitVec.ofNat 32 next :=
          d_next p0 off hsmall
        have hpro : prologue mem o' off = (m8, BitVec.ofNat 32 next) := by
          have hi := (ht off hsmall).1
          have hd := (ht off hsmall).2
          simp only [prologue, hbig, ite_false, hM, hi, hd, BitVec.ofNat_add_ofNat,
            ofNat32_toNat (show o' - off < 2 ^ 32 by omega),
            ofNat32_toNat (show o' - off + inc32[off]! < 2 ^ 32 by omega),
            d_next _ _ hsmall]
          rfl
        have hs8 : m8.size = mem.size := by simp only [m8, fwdCopy_size, hs4]
        simp only [FVA.Wasm.Exec.Ref.setMem_setMem]
        change Until H _ _ ((ctx5 (ctx2 F)).fill
          ⟨st.setMem ma m8,
            ⟨dLs src dst n cap cpy j m o' (BitVec.ofNat 32 p) v16 (vI (4 * off)), inst⟩,
            .label 0 [] (.label 0 [] (vals [vI (o' + 4)] ++ (dSmall.drop 36).map .plain) ::
              dLarge.map .plain) :: dAfterPrologue.map .plain⟩)
        wasm_eval 7 [block_simp, dSmall, dLs, hm, hmem, hs8, hreadDec, hnext]
        · simp [TraceOK, AccessOK, ReadSet, Span]
          intro x hx0 hx1
          left
          omega
        · apply Until.done
          refine ⟨vI (4 * off), ?_⟩
          simp only [hpro, dLs, BContext.fill]

end Subjects.Lz4C.Eval
