import FVATest.Subjects.Lz4C.Eval.SegDPrologue

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
set_option linter.unusedSimpArgs false

/-- The near-end byte loop leaves its final branch to its caller's label context. -/
theorem d_bytes (H : HostSem) (C : Context) (st : Store) (inst : ModuleInst) (ls : List Val)
    (ma : Nat) (mem : MemInst) (src dst n cap p q e k : Nat)
    (h2 : ls[2]? = some (vI p)) (h18 : ls[18]? = some (vI q)) (h3 : ls[3]? = some (vI e))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hp0 : dst ≤ p) (hq0 : dst ≤ q) (hp1 : p + k ≤ dst + cap) (hq1 : q + k ≤ dst + cap)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size < 2 ^ 32) (he : e = q + k) (hk : 0 < k) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (fun c => c = C.fill
        ⟨st.setMem ma (fwdCopy mem q p k),
          ⟨(ls.set 18 (vI (q + k))).set 2 (vI (p + k)), inst⟩,
          [.label 0 [dByteLoop] [.plain (.br 2)]]⟩)
      (C.fill ⟨st, ⟨ls, inst⟩, [.plain dByteLoop]⟩) := by
  have hl2 : 2 < ls.length := (List.getElem?_eq_some_iff.mp h2).1
  have hl18 : 18 < ls.length := (List.getElem?_eq_some_iff.mp h18).1
  induction k generalizing st mem ls p q with
  | zero => omega
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      wasm_eval 15 [block_simp, dByteLoop, dByteBody, h2, h18, h3, hm, hmem]
      · simp [TraceOK, AccessOK, ReadSet, Span]
        constructor
        · intro x hx0 hx1
          right; right
          constructor <;> omega
        · intro x hx0 hx1
          constructor <;> omega
      · apply Until.done
        rw [List.set_comm (vI (p + 1)) (vI (q + 1)) (by decide : (2 : Nat) ≠ 18)]
        rfl
    · wasm_eval 16 [block_simp, dByteLoop, dByteBody, h2, h18, h3, hm, hmem]
      · simp [TraceOK, AccessOK, ReadSet, Span]
        constructor
        · intro x hx0 hx1
          right; right
          constructor <;> omega
        · intro x hx0 hx1
          constructor <;> omega
      · let ls' := (ls.set 2 (vI (p + 1))).set 18 (vI (q + 1))
        have h2' : ls'[2]? = some (vI (p + 1)) := by
          simp only [ls', List.getElem?_set_ne (by decide : (18 : Nat) ≠ 2),
            List.getElem?_set_self hl2]
        have h18' : ls'[18]? = some (vI (q + 1)) :=
          List.getElem?_set_self (by simpa only [List.length_set] using hl18)
        have h3' : ls'[3]? = some (vI e) := by
          simpa only [ls', List.getElem?_set_ne (by decide : (18 : Nat) ≠ 3),
            List.getElem?_set_ne (by decide : (2 : Nat) ≠ 3)] using h3
        have hi := ih (st.setMem ma (mem.write q 1 (mem.byte p).toNat))
          ls' (mem.write q 1 (mem.byte p).toNat) (p + 1) (q + 1) h2' h18' h3'
          (setMem_get hmem _) (by omega) (by omega) (by omega) (by omega)
          (by simpa only [write_size] using hend) (by simpa only [write_size] using hsize)
          (by omega) (by omega) (by simpa only [ls', List.length_set] using hl2)
          (by simpa only [ls', List.length_set] using hl18)
        apply hi.mono (fun _ hx => hx)
        intro c hc
        simp only [ls', FVA.Wasm.Exec.Ref.setMem_setMem,
          local_pair_reset _ _ _ _ _ _ _ (by decide : (18 : Nat) ≠ 2)] at hc
        simpa only [fwdCopy, Nat.add_assoc, Nat.add_comm 1 k] using hc

noncomputable def dHeadPost (F : Context) (st : Store) (inst : ModuleInst)
    (src dst n cap cpy j : Nat) (c : Config) : Prop :=
  ∃ ls, HeadLocals ls src dst n cap cpy j ∧
    c = (ctx4 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩, [.plain mainLoop]⟩

theorem d_finish_near (H : HostSem) (F : Context) (st : Store) (inst : ModuleInst)
    (ls : List Val) (ma : Nat) (mem : MemInst) (src dst n cap cpy j p q : Nat)
    (hcl : ConstLocals ls src dst n cap) (h2 : ls[2]? = some (vI p))
    (h18 : ls[18]? = some (vI q)) (h3 : ls[3]? = some (vI cpy)) (h4 : ls[4]? = some (vI j))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hp0 : dst ≤ p) (hpq : p ≤ q) (hq1 : q ≤ dst + cap) (hc1 : cpy ≤ dst + cap)
    (hend : dst + cap ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (ReadSet ma src n dst cap) (Span ma dst cap))
      (dHeadPost F (st.setMem ma (if q < cpy then fwdCopy mem q p (cpy - q) else mem))
        inst src dst n cap cpy j)
      ((ctx4 (ctx2 F)).fill ⟨st, ⟨ls, inst⟩,
        .label 0 [mainLoop] (.label 0 [] ((dNear.drop 9).map .plain) :: dAfterNear.map .plain) ::
          (body4.drop 1).map .plain⟩) := by
  rw [main_tail]
  by_cases hgo : q < cpy
  · wasm_eval 4 [block_simp, dNear, h2, h18, h3, hgo, igeU]
    · simp [TraceOK, AccessOK]
    · let C := Context.label 0 [] (dAfterNear.map .plain) (ctx5 (ctx2 F))
      change Until H _ _ (C.fill ⟨st, ⟨ls, inst⟩, [.plain dByteLoop]⟩)
      apply (d_bytes H C st inst ls ma mem src dst n cap p q cpy (cpy - q)
        h2 h18 h3 hm hmem hp0 (by omega) (by omega) (by omega) hend hsize (by omega)
          (by omega)).trans
      intro c hc
      subst c
      change Until H _ _ ((ctx4 (ctx2 F)).fill ⟨_, _,
        [.label 0 [mainLoop] (.label 0 [] [.label 0 [dByteLoop] [.plain (.br 2)]] ::
          dAfterNear.map .plain)]⟩)
      wasm_eval 1 [block_simp]
      · simp [TraceOK, AccessOK]
      · apply Until.done
        refine ⟨(ls.set 18 (vI (q + (cpy - q)))).set 2 (vI (p + (cpy - q))), ?_, ?_⟩
        · apply HeadLocals.of_const
          · exact (hcl.set (by omega) _).set (by omega) _
          · simpa only [List.getElem?_set_ne (by decide : (2 : Nat) ≠ 3),
              List.getElem?_set_ne (by decide : (18 : Nat) ≠ 3)] using h3
          · simpa only [List.getElem?_set_ne (by decide : (2 : Nat) ≠ 4),
              List.getElem?_set_ne (by decide : (18 : Nat) ≠ 4)] using h4
        · simp only [hgo, ite_true, BContext.fill]
  · wasm_eval 5 [block_simp, dNear, h2, h18, h3, hgo, igeU]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      refine ⟨ls, HeadLocals.of_const hcl h3 h4, ?_⟩
      simp only [hgo, ite_false, FVA.Wasm.Exec.Ref.setMem_self hmem, BContext.fill]

end Subjects.Lz4C.Eval
