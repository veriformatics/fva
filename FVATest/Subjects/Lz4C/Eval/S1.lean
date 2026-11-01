import FVATest.Subjects.Lz4C.Eval.CopyFacts

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- The byte tail, with every caller label and operand stack preserved. -/
theorem cp1_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s r : Nat) (u0 u1 u5 u6 : Val) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + r ≤ mem.size) (hs : s + r ≤ mem.size) (hsize : mem.size < 2 ^ 32) (hr : 0 < r) :
    Until H (Within (Span ma s r) (Span ma d r))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem d s r),
        ⟨[u0, u1, vI (s + r), vI 0, vI (d + r), u5, u6], inst⟩, rest⟩)
      (C.fill ⟨st, ⟨[u0, u1, vI s, vI r, vI d, u5, u6], inst⟩,
        [.plain (.loop .empty cp1)] ++ rest⟩) := by
  induction r generalizing st mem d s with
  | zero => omega
  | succ r ih =>
    by_cases hz : r = 0
    · subst r
      wasm_eval 17 [block_simp, cp1, hm, hmem]
      · simp [TraceOK, AccessOK, Span]
        constructor <;> intro a hlo hhi <;> constructor <;> omega
      · exact .done rfl
    · wasm_eval 17 [block_simp, cp1, hm, hmem, Nat.add_sub_cancel]
      · simp [TraceOK, AccessOK, Span]
        constructor <;> intro a hlo hhi <;> constructor <;> omega
      · have hi := ih (st.setMem ma (mem.write d 1 (mem.byte s).toNat))
          (mem.write d 1 (mem.byte s).toNat) (d + 1) (s + 1)
          (setMem_get hmem _)
            (by simpa only [write_size] using (show d + 1 + r ≤ mem.size by omega))
          (by simpa only [write_size] using (show s + 1 + r ≤ mem.size by omega))
          (by simpa only [write_size] using hsize) (by omega)
        apply hi.mono
        · intro c hc
          refine ⟨fun m a h => ?_, fun m a h => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a h
            exact ⟨rfl, by omega, by omega⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a h
            exact ⟨rfl, by omega, by omega⟩
        · intro c hc
          simpa only [fwdCopy, setMem_setMem, Nat.add_assoc, Nat.add_comm 1 r] using hc

/-- The four-byte loop. The two scratch locals are overwritten by every iteration. -/
theorem cp4_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s i e r k : Nat) (u2 u6 : Val) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + e ≤ mem.size) (hs : s + e ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (he : e = i + 4 * k) (hk : 0 < k) :
    Until H (Within (Span ma (s + i) (4 * k)) (Span ma (d + i) (4 * k)))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem (d + i) (s + i) (4 * k)),
        ⟨[vI d, vI s, vI (d + e - 4), vI r, vI e, vI e, vI (s + e - 4)], inst⟩, rest⟩)
      (C.fill ⟨st, ⟨[vI d, vI s, u2, vI r, vI i, vI e, u6], inst⟩,
        [.plain (.loop .empty cp4)] ++ rest⟩) := by
  induction k generalizing st mem i u2 u6 with
  | zero => omega
  | succ k ih =>
    have hb0 : ¬ mem.size < s + i + 1 := by omega
    have hb1 : ¬ mem.size < s + i + 1 + 1 := by omega
    have hb2 : ¬ mem.size < s + i + 2 + 1 := by omega
    have hb3 : ¬ mem.size < s + i + 3 + 1 := by omega
    have hw0 : ¬ mem.size < d + i + 1 := by omega
    have hw1 : ¬ mem.size < d + i + 1 + 1 := by omega
    have hw2 : ¬ mem.size < d + i + 2 + 1 := by omega
    have hw3 : ¬ mem.size < d + i + 3 + 1 := by omega
    by_cases hz : k = 0
    · subst k
      wasm_eval 39 [block_simp, cp4, hm, hmem, hb0, hb1, hb2, hb3, hw0, hw1, hw2, hw3]
      · simp [TraceOK, AccessOK, Span]
        repeat' constructor
        all_goals intro a hlo hhi
        all_goals constructor <;> omega
      · apply Until.done
        have he1 : i + 4 = e := by omega
        have hd1 : d + e - 4 = d + i := by omega
        have hs1 : s + e - 4 = s + i := by omega
        simp only [Nat.mul_one, he1, hd1, hs1]
    · wasm_eval 39 [block_simp, cp4, hm, hmem, hb0, hb1, hb2, hb3, hw0, hw1, hw2, hw3]
      · simp [TraceOK, AccessOK, Span]
        repeat' constructor
        all_goals intro a hlo hhi
        all_goals constructor <;> omega
      · have hi := ih (st.setMem ma (fwdCopy mem (d + i) (s + i) 4))
          (fwdCopy mem (d + i) (s + i) 4) (i + 4) (vI (d + i)) (vI (s + i))
          (setMem_get hmem _) (by simpa only [fwdCopy_size] using hd)
          (by simpa only [fwdCopy_size] using hs) (by simpa only [fwdCopy_size] using hsize)
          (by omega) (by omega)
        apply hi.mono
        · intro c hc
          refine ⟨fun m a h => ?_, fun m a h => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a h
            exact ⟨rfl, by omega, by omega⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a h
            exact ⟨rfl, by omega, by omega⟩
        · intro c hc
          rw [setMem_setMem] at hc
          have hm4 := fwdCopy_add mem (d + i) (s + i) 4 (4 * k)
          simp only [Nat.add_assoc] at hm4
          rw [← hm4] at hc
          simpa only [show 4 * (k + 1) = 4 + 4 * k by omega] using hc

def CpPost (C : BContext) (st : Store) (inst : ModuleInst) (d s : Nat) (c : Config) : Prop :=
  ∃ u2 u3 u4 u5 u6 : Val,
    c = C.fill ⟨st, ⟨[vI d, vI s, u2, u3, u4, u5, u6], inst⟩, vals [vI d]⟩

/-- Enter the tail with an already-processed prefix of length `i`. -/
theorem cp_tail_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s i r : Nat) (u2 u5 u6 : Val)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + i + r ≤ mem.size) (hs : s + i + r ≤ mem.size)
    (hsize : mem.size < 2 ^ 32) (hr : 0 < r) :
    Until H (Within (Span ma (s + i) r) (Span ma (d + i) r))
      (CpPost C (st.setMem ma (fwdCopy mem (d + i) (s + i) r)) inst d s)
      ((BContext.label [] 0 [] [.plain (.localGet 0)] C).fill
        ⟨st, ⟨[vI d, vI s, u2, vI r, vI i, u5, u6], inst⟩, (cpOuter.drop 10).map .plain⟩) := by
  wasm_eval 8 [block_simp, cpOuter, hm, hmem]
  · simp [TraceOK, AccessOK]
  · apply (cp1_until H (BContext.label [] 0 [] [.plain (.localGet 0)] C) st inst ma mem
        (d + i) (s + i) r (vI d) (vI s) u5 u6 [] hm hmem hd hs hsize hr).trans
    intro c hc
    subst c
    change Until H _ _ (C.fill ⟨_, _, [.label 0 [] [], .plain (.localGet 0)]⟩)
    wasm_eval 2 [block_simp]
    · simp [TraceOK, AccessOK]
    · exact .done ⟨_, _, _, _, _, rfl⟩

/-- Entire compiled callee body; only the five dead scratch locals are hidden. -/
theorem cp_body_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s n : Nat)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + n ≤ mem.size) (hs : s + n ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (Span ma s n) (Span ma d n))
      (CpPost C (st.setMem ma (fwdCopy mem d s n)) inst d s)
      (C.fill ⟨st, ⟨[vI d, vI s, vI n, vI 0, vI 0, vI 0, vI 0], inst⟩,
        cpBody.map .plain⟩) := by
  by_cases hn : n = 0
  · subst n
    wasm_eval 6 [block_simp, cpBody, cpOuter, hm, hmem]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      refine ⟨vI 0, vI 0, vI 0, vI 0, vI 0, ?_⟩
      simp only [fwdCopy, setMem_self hmem]
      rfl
  · by_cases hn4 : n < 4
    · wasm_eval 13 [block_simp, cpBody, cpOuter, cpBlock, hm, hmem, hn, hn4]
      · simp [TraceOK, AccessOK]
      · change Until H _ _ ((BContext.label [] 0 [] [.plain (.localGet 0)] C).fill
          ⟨st, ⟨[vI d, vI s, vI n, vI (n % 4), vI 0, vI 0, vI 0], inst⟩,
            (cpOuter.drop 10).map .plain⟩)
        have hr : n % 4 = n := Nat.mod_eq_of_lt hn4
        simpa only [hr, Nat.add_zero] using
          cp_tail_until H C st inst ma mem d s 0 n (vI n) (vI 0) (vI 0) hm hmem
            (by omega) (by omega) hsize (by omega)
    · wasm_eval 16 [block_simp, cpBody, cpOuter, cpBlock, hm, hmem, hn, hn4]
      · simp [TraceOK, AccessOK]
      · let C1 := BContext.label [] 0 [] [.plain (.localGet 0)] C
        let C2 := BContext.label [] 0 [] ((cpOuter.drop 10).map .plain) C1
        change Until H _ _ (C2.fill
          ⟨st, ⟨[vI d, vI s, vI n, vI (n % 4), vI 0, vI (4 * (n / 4)), vI 0], inst⟩,
            [.plain (.loop .empty cp4)] ++ [.plain (.localGet 3), .plain (.itestEqz .w32),
              .plain (.brIf 1)]⟩)
        apply (cp4_until H C2 st inst ma mem d s 0 (4 * (n / 4)) (n % 4) (n / 4)
          (vI n) (vI 0) [.plain (.localGet 3), .plain (.itestEqz .w32), .plain (.brIf 1)]
          hm hmem (by omega) (by omega) hsize (by omega) (by omega)).mono
          (fun c hc => ⟨fun m a ha => by
            obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a ha
            exact ⟨rfl, by omega, by omega⟩,
          fun m a ha => by
            obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a ha
            exact ⟨rfl, by omega, by omega⟩⟩) (fun _ hx => hx) |>.trans
        intro c hc
        subst c
        by_cases hr : n % 4 = 0
        · change Until H _ _ (C.fill ⟨_, _, [.label 0 []
            ([.label 0 [] [.plain (.localGet 3), .plain (.itestEqz .w32), .plain (.brIf 1)]] ++
              (cpOuter.drop 10).map .plain), .plain (.localGet 0)]⟩)
          wasm_eval 5 [block_simp, hr]
          · simp [TraceOK, AccessOK]
          · apply Until.done
            have he : 4 * (n / 4) = n := by omega
            refine ⟨vI (d + 4 * (n / 4) - 4), vI 0, vI (4 * (n / 4)),
              vI (4 * (n / 4)), vI (s + 4 * (n / 4) - 4), ?_⟩
            simp only [Nat.add_zero, he]
            rfl
        · change Until H _ _ (C1.fill ⟨_, _,
            [.label 0 [] [.plain (.localGet 3), .plain (.itestEqz .w32), .plain (.brIf 1)]] ++
              (cpOuter.drop 10).map .plain⟩)
          wasm_eval 4 [block_simp, hr]
          · simp [TraceOK, AccessOK]
          · have ht := cp_tail_until H C (st.setMem ma (fwdCopy mem d s (4 * (n / 4))))
              inst ma (fwdCopy mem d s (4 * (n / 4))) d s (4 * (n / 4)) (n % 4)
              (vI (d + 4 * (n / 4) - 4)) (vI (4 * (n / 4)))
              (vI (s + 4 * (n / 4) - 4)) hm (setMem_get hmem _)
              (by simp only [fwdCopy_size]; omega) (by simp only [fwdCopy_size]; omega)
              (by simpa only [fwdCopy_size] using hsize) (by omega)
            apply ht.mono
            · intro c hc
              refine ⟨fun m a ha => ?_, fun m a ha => ?_⟩
              · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a ha
                exact ⟨rfl, by omega, by omega⟩
              · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a ha
                exact ⟨rfl, by omega, by omega⟩
            · intro c hc
              simpa only [CpPost, setMem_setMem, ← fwdCopy_add,
                show 4 * (n / 4) + n % 4 = n by omega] using hc

theorem s1 : MemcpyS1 := by
  intro H C st f vs rest a ma inst mem d s n hcall hfun hm hmem hd hs hsize
  wasm_eval 2 [block_simp, hcall, hfun, copyType, cpBody_eq, cpDefaults_eq, cpLocals_eq,
    List.take_left, List.drop_left, List.take_left', List.drop_left']
  · simp [TraceOK, AccessOK]
  · let B := BContext.label [] 1 [] [] (BContext.frame vs 1 f rest (.base C))
    change Until H _ _ (B.fill ⟨st,
      ⟨[vI d, vI s, vI n, vI 0, vI 0, vI 0, vI 0], inst⟩, cpBody.map .plain⟩)
    apply (cp_body_until H B st inst ma mem d s n hm hmem hd hs hsize).trans
    intro c hc
    obtain ⟨u2, u3, u4, u5, u6, rfl⟩ := hc
    change Until H _ _ (C.fill ⟨_, f, vals vs ++
      (.frame 1 ⟨[vI d, vI s, u2, u3, u4, u5, u6], inst⟩ [.label 1 [] (vals [vI d])] :: rest)⟩)
    wasm_eval 2 [block_simp]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      simp only [vals, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, BContext.fill]

#print axioms s1

end Subjects.Lz4C.Eval
