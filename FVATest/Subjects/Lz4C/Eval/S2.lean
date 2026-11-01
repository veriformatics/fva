import FVATest.Subjects.Lz4C.Eval.BackwardBody2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem mp_body_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s n : Nat)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + n ≤ mem.size) (hs : s + n ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (Span ma s n) (Span ma d n))
      (MvPost C (st.setMem ma (move mem d s n)) inst d)
      (C.fill ⟨st, ⟨[vI d, vI s, vI n, vI 0, vI 0, vI 0, vI 0], inst⟩,
        mpBody.map .plain⟩) := by
  by_cases hds : d < s
  · wasm_eval 7 [block_simp, mpBody, mpOuter, mbInner, hds]
    · simp [TraceOK, AccessOK]
    · apply (mp_forward_until H C st inst ma mem d s n hm hmem hd hs hsize).mono (fun _ hx => hx)
      intro c hc
      obtain ⟨u2, u3, u4, u5, u6, hc⟩ := hc
      refine ⟨vI s, u2, u3, u4, u5, u6, ?_⟩
      simpa only [fwdCopy_eq_move mem d s n (by omega)] using hc
  · wasm_eval 6 [block_simp, mpBody, mpOuter, mbInner, hds]
    · simp [TraceOK, AccessOK]
    · apply (mb_path_until H C st inst ma mem d s n hm hmem hd hs hsize).mono (fun _ hx => hx)
      intro c hc
      simpa only [MvPost, backCopy_eq_move mem d s n (by omega)] using hc

theorem s2 : MemmoveS2 := by
  intro H C st f vs rest a ma inst mem d s n hcall hfun hm hmem hd hs hsize
  wasm_eval 2 [block_simp, hcall, hfun, copyType, mpBody_eq, mpLocals_eq,
    List.take_left, List.drop_left, List.take_left', List.drop_left']
  · simp [TraceOK, AccessOK]
  · let B := BContext.label [] 1 [] [] (BContext.frame vs 1 f rest (.base C))
    change Until H _ _ (B.fill ⟨st,
      ⟨[vI d, vI s, vI n, vI 0, vI 0, vI 0, vI 0], inst⟩, mpBody.map .plain⟩)
    apply (mp_body_until H B st inst ma mem d s n hm hmem hd hs hsize).trans
    intro c hc
    obtain ⟨u1, u2, u3, u4, u5, u6, rfl⟩ := hc
    change Until H _ _ (C.fill ⟨_, f, vals vs ++
      (.frame 1 ⟨[vI d, u1, u2, u3, u4, u5, u6], inst⟩ [.label 1 [] (vals [vI d])] :: rest)⟩)
    wasm_eval 2 [block_simp]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      simp only [vals, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, BContext.fill]

#print axioms s2

end Subjects.Lz4C.Eval
