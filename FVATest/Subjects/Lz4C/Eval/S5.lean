import FVATest.Subjects.Lz4C.Eval.ShortFacts

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem s5 : ShortcutS5 := by
  intro H C st inst ls a ma mem src dst n cap op ip hhead hcall hfun hm hmem
    hsrc hdst hsrcend hdstend hsize hsep hiplo hiphi hoplo hophi
  obtain ⟨u2, u15, u16, u17, u18, rfl⟩ := head_decompose hhead
  let t := (mem.byte ip).toNat
  have ht : t < 256 := (mem.byte ip).toNat_lt
  have hllrange : t / 16 < 16 := by omega
  have hmlrange : t % 16 < 16 := by omega
  by_cases hll : (mem.byte ip).toNat / 16 = 15
  · wasm_eval 18 [block_simp, ↓ short_instr_step, ↓ short_toVal, ↓ short_unique, ↓ short_access,
      short_ne_br, short_ne_return, short_body5, short_body6, short_body7,
      short_body8, shortCode, hm, hmem, hll]
    · simp [TraceOK, AccessOK, Span]
      intro x hlo hhi
      left
      constructor <;> omega
    · apply Until.done
      left
      refine ⟨hll, ?_⟩
      simp only [wasm_step, hll, BContext.fill, ctx8, ctx4, Context.fill, shortRest5,
        shortRest6, shortRest7, shortRest8, main_tail]
  · have hlllt : t / 16 < 15 := by omega
    wasm_eval 17 [block_simp, ↓ short_instr_step, ↓ short_toVal, ↓ short_unique, ↓ short_access,
      short_ne_br, short_ne_return, short_body5, short_body6, short_body7,
      short_body8, shortCode, hm, hmem, hll]
    · simp [TraceOK, AccessOK, Span]
      intro x hlo hhi
      left
      constructor <;> omega
    · change Until H _ _ ((shortCtx C).fill
        ⟨st, ⟨tokenLs src dst n cap op ip t (t / 16) u17 u18, inst⟩,
          (shortCode.drop 9).map .plain⟩)
      by_cases hri : ip + 1 + 16 < src + n
      · wasm_eval 6 [block_simp, shortCode, tokenLs, hri]
        · simp [TraceOK, AccessOK]
        · by_cases hro : op + 32 ≤ dst + cap
          · wasm_eval 6 [block_simp, shortCode, tokenLs, hro]
            · simp [TraceOK, AccessOK]
            · wasm_eval 2 [block_simp]
              · simp [TraceOK, AccessOK]
              · apply (short_copy H (shortCtx C) st inst
                  (tokenLs src dst n cap op ip t (t / 16) u17 u18) a ma mem src dst n cap
                  op (ip + 1) 16 ((shortCode.drop 15).map .plain) hcall hfun hm hmem
                  (by omega) (by omega) hsize (.inl ⟨by omega, by omega⟩) ⟨hoplo, by omega⟩).trans
                intro c hc
                subst c
                let off := (mem.byte (ip + 1 + t / 16)).toNat +
                  256 * (mem.byte (ip + 2 + t / 16)).toNat
                have ho : off < 65536 := by
                  have hb0 := (mem.byte (ip + 1 + t / 16)).toNat_lt
                  have hb1 := (mem.byte (ip + 2 + t / 16)).toNat_lt
                  dsimp only [off]
                  omega
                have hom : off ≤ op + t / 16 := by omega
                have hipoff : ip + 1 + t / 16 + 1 = ip + 2 + t / 16 := by omega
                have hread : (fwdCopy mem op (ip + 1) 16).read (ip + 1 + t / 16) 2 = off := by
                  rw [read_two,
                    copy_source_byte mem src dst n cap op (ip + 1) 16 (ip + 1 + t / 16)
                      hsep hoplo (by omega) (by omega) (by omega),
                    copy_source_byte mem src dst n cap op (ip + 1) 16 (ip + 1 + t / 16 + 1)
                      hsep hoplo (by omega) (by omega) (by omega), hipoff]
                have hM := ofNat32_sub (a := op + t / 16) (b := off) (by omega) hom
                dsimp only [t, off] at hM
                have hip2 : ip + 1 + t / 16 + 2 = ip + 3 + t / 16 := by omega
                wasm_eval 24 [block_simp, shortCode, tokenLs, hm, hmem, hread, hip2]
                · simp [TraceOK, AccessOK, Span]
                  intro x hlo hhi
                  left
                  constructor <;> omega
                · by_cases hml : t % 16 = 15
                  · dsimp only [t] at hml
                    change Until H _ _ ((ctx6 C).fill ⟨_, _,
                      .label 0 [] (.label 0 [] (.label 0 []
                        (vals [.i32 (bool (decide (t % 16 = 15)))] ++
                          (shortCode.drop 38).map .plain) :: shortRest8.map .plain) ::
                            shortRest7.map .plain) :: shortRest6.map .plain⟩)
                    wasm_eval 2 [block_simp, shortCode, hml]
                    · simp [TraceOK, AccessOK]
                    · apply Until.done
                      right; right; left
                      refine ⟨hlllt, hri, hro, .inl hml, ?_⟩
                      simp only [t, wasm_step, hM, hml, BContext.fill, shortRest6]; rfl
                  · have hmllt : t % 16 < 15 := by omega
                    wasm_eval 1 [block_simp, hml]
                    · simp [TraceOK, AccessOK]
                    · by_cases hoff : off < 8
                      · change Until H _ _ ((ctx6 C).fill ⟨_, _,
                          .label 0 [] (.label 0 [] (.label 0 []
                            ((shortCode.drop 39).map .plain) :: shortRest8.map .plain) ::
                              shortRest7.map .plain) :: shortRest6.map .plain⟩)
                        wasm_eval 4 [block_simp, shortCode, hoff]
                        · simp [TraceOK, AccessOK]
                        · apply Until.done
                          right; right; left
                          refine ⟨hlllt, hri, hro, .inr hoff, ?_⟩
                          simp only [wasm_step, hM, BContext.fill, shortRest6]; rfl
                      · have hoff8 : 8 ≤ off := by omega
                        wasm_eval 3 [block_simp, hoff]
                        · simp [TraceOK, AccessOK]
                        · by_cases hbefore : op + t / 16 < dst + off
                          · change Until H _ _ ((ctx5 C).fill ⟨_, _,
                              .label 0 [] (.label 0 [] (.label 0 [] (.label 0 []
                                ((shortCode.drop 43).map .plain) :: shortRest8.map .plain) ::
                                  shortRest7.map .plain) :: shortRest6.map .plain) ::
                                    shortRest5.map .plain⟩)
                            wasm_eval 5 [block_simp, shortCode, hbefore]
                            · simp [TraceOK, AccessOK]
                            · apply Until.done
                              right; right; right; left
                              refine ⟨hlllt, hri, hro, hmllt, hoff8, hbefore, ?_⟩
                              simp only [wasm_step, hM, BContext.fill, shortRest5]; rfl
                          · have hafter : dst + off ≤ op + t / 16 := by omega
                            wasm_eval 4 [block_simp, hbefore]
                            · simp [TraceOK, AccessOK]
                            · let D := op + t / 16
                              let M := op + t / 16 - off
                              let mem16 := fwdCopy mem op (ip + 1) 16
                              have hMlo : dst ≤ M := by dsimp only [M]; omega
                              have hD18 : D + 18 ≤ dst + cap := by dsimp only [D]; omega
                              change Until H _ _ ((shortCtx C).fill
                                ⟨st.setMem ma mem16, ⟨matchLs src dst n cap op ip t off, inst⟩,
                                  (shortCode.drop 47).map .plain⟩)
                              wasm_eval 2 [block_simp, shortCode, matchLs]
                              · simp [TraceOK, AccessOK]
                              · apply (short_copy H (shortCtx C) (st.setMem ma mem16) inst
                                  (matchLs src dst n cap op ip t off) a ma mem16 src dst n cap
                                  D M 8 ((shortCode.drop 51).map .plain) hcall
                                  (by simpa only [setMem_funcs] using hfun) hm (setMem_get hmem _)
                                  (by simp only [mem16, fwdCopy_size]; omega)
                                  (by simp only [mem16, fwdCopy_size]; dsimp only [D,
                                    M] at *; omega)
                                  (by simpa only [mem16, fwdCopy_size] using hsize)
                                  (.inr ⟨hMlo, by dsimp only [M] at *; omega⟩)
                                  ⟨by dsimp only [D]; omega, by omega⟩).trans
                                intro c hc
                                subst c
                                let mem8 := fwdCopy mem16 D M 8
                                wasm_eval 5 [block_simp, shortCode, matchLs]
                                · simp [TraceOK, AccessOK]
                                · apply (short_copy H (shortCtx C) (st.setMem ma mem8) inst
                                    (matchLs src dst n cap op ip t off) a ma mem8 src dst n cap
                                    (D + 8) (M + 8) 8 ((shortCode.drop 60).map .plain) hcall
                                    (by simpa only [setMem_funcs] using hfun) hm (setMem_get hmem _)
                                    (by simp only [mem8, mem16, fwdCopy_size]; omega)
                                    (by simp only [mem8, mem16, fwdCopy_size]; dsimp only [D,
                                      M] at *; omega)
                                    (by simpa only [mem8, mem16, fwdCopy_size] using hsize)
                                    (.inr ⟨by omega, by dsimp only [M] at *; omega⟩)
                                    ⟨by dsimp only [D]; omega, by omega⟩).trans
                                  intro c hc
                                  subst c
                                  have hcomp16 : fwdCopy mem8 (D + 8) (M + 8) 8 =
                                      fwdCopy mem16 D M 16 := by
                                    exact (fwdCopy_add mem16 D M 8 8).symm
                                  simp only [setMem_setMem, hcomp16]
                                  wasm_eval 5 [block_simp, shortCode, matchLs]
                                  · simp [TraceOK, AccessOK]
                                  · apply (short_copy H (shortCtx C)
                                      (st.setMem ma (fwdCopy mem16 D M 16)) inst
                                      (matchLs src dst n cap op ip t off) a ma
                                      (fwdCopy mem16 D M 16) src dst n cap (D + 16) (M + 16) 2
                                      ((shortCode.drop 69).map .plain) hcall
                                      (by simpa only [setMem_funcs] using hfun) hm
                                      (setMem_get hmem _)
                                      (by simp only [mem16, fwdCopy_size]; omega)
                                      (by simp only [mem16, fwdCopy_size]; dsimp only [D,
                                        M] at *; omega)
                                      (by simpa only [mem16, fwdCopy_size] using hsize)
                                      (.inr ⟨by omega, by dsimp only [M] at *; omega⟩)
                                      ⟨by dsimp only [D]; omega, by omega⟩).trans
                                    intro c hc
                                    subst c
                                    have hcomp18 :
                                        fwdCopy (fwdCopy mem16 D M 16) (D + 16) (M + 16) 2 =
                                        fwdCopy mem16 D M 18 := by
                                      exact (fwdCopy_add mem16 D M 16 2).symm
                                    simp only [setMem_setMem, hcomp18]
                                    change Until H _ _ ((ctx4 C).fill ⟨_, _,
                                      [.label 0 [mainLoop] (.label 0 [] (.label 0 [] (.label 0 []
                                        (.label 0 [] (vals [vI (D + 16)]
                                          ++ (shortCode.drop 69).map .plain) ::
                                          shortRest8.map .plain) :: shortRest7.map .plain) ::
                                            shortRest6.map .plain) :: shortRest5.map .plain)]⟩)
                                    wasm_eval 7 [block_simp, shortCode, matchLs]
                                    · simp [TraceOK, AccessOK]
                                    · apply Until.done
                                      right; right; right; right
                                      refine ⟨hlllt, hri, hro, hmllt, hoff8, hafter, ?_⟩
                                      simp only [wasm_step, hM, BContext.fill, matchLs, mem16, D, M]
                                      rfl
          · change Until H _ _ ((ctx7 C).fill ⟨st, _,
              .label 0 [] (.label 0 [] ((shortCode.drop 10).map .plain) ::
                shortRest8.map .plain) :: shortRest7.map .plain⟩)
            wasm_eval 8 [block_simp, shortCode, tokenLs, hro]
            · simp [TraceOK, AccessOK]
            · apply Until.done
              right; left
              refine ⟨hlllt, fun h => hro h.2, ?_⟩
              simp only [wasm_step, BContext.fill, shortRest7]
              rfl
      · change Until H _ _ ((ctx7 C).fill ⟨st, _,
          .label 0 [] (.label 0 [] ((shortCode.drop 9).map .plain) ::
            shortRest8.map .plain) :: shortRest7.map .plain⟩)
        wasm_eval 8 [block_simp, shortCode, tokenLs, hri]
        · simp [TraceOK, AccessOK]
        · apply Until.done
          right; left
          refine ⟨hlllt, fun h => hri h.1, ?_⟩
          simp only [wasm_step, BContext.fill, shortRest7]
          rfl

#print axioms s5

end Subjects.Lz4C.Eval
