import FVATest.Subjects.Lz4C.Eval.Forward2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Enter the tail with an already-processed prefix of length `i`. -/
theorem mp_tail_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s i r : Nat) (u2 u3 u5 : Val)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + i + r ≤ mem.size) (hs : s + i + r ≤ mem.size)
    (hsize : mem.size < 2 ^ 32) (hr : 0 < r) :
    Until H (Within (Span ma (s + i) r) (Span ma (d + i) r))
      (CpPost C (st.setMem ma (fwdCopy mem (d + i) (s + i) r)) inst d s)
      ((BContext.label [] 0 [] [.plain (.localGet 0)] C).fill
        ⟨st, ⟨[some (vI d), some (vI s), some u2, some u3, some (vI i), some u5, some (vI r)],
            inst⟩, mpTail.map .plain⟩) := by
  wasm_eval 8 [block_simp, mpTail, hm, hmem]
  · simp [TraceOK, AccessOK]
  · apply (mp1_until H (BContext.label [] 0 [] [.plain (.localGet 0)] C) st inst ma mem
        (d + i) (s + i) r (vI d) (vI s) u2 u5 [] hm hmem hd hs hsize hr).trans
    intro c hc
    subst c
    change Until H _ _ (C.fill ⟨_, _, [.label 0 [] [], .plain (.localGet 0)]⟩)
    wasm_eval 2 [block_simp]
    · simp [TraceOK, AccessOK]
    · exact .done ⟨_, _, _, _, _, rfl⟩

/-- Entire compiled callee body; only the five dead scratch locals are hidden. -/
theorem mp_forward_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s n : Nat)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + n ≤ mem.size) (hs : s + n ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (Span ma s n) (Span ma d n))
      (CpPost C (st.setMem ma (fwdCopy mem d s n)) inst d s)
      (C.fill ⟨st,
          ⟨[some (vI d), some (vI s), some (vI n), some (vI 0), some (vI 0), some (vI 0),
          some (vI 0)], inst⟩,
        [.label 0 [] (mpForward.map .plain), .plain (.localGet 0)]⟩) := by
  by_cases hn : n = 0
  · subst n
    wasm_eval 5 [block_simp, mpForward, hm, hmem]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      refine ⟨vI 0, vI 0, vI 0, vI 0, vI 0, ?_⟩
      simp only [fwdCopy, setMem_self hmem]
      rfl
  · by_cases hn4 : n < 4
    · wasm_eval 12 [block_simp, mpForward, mpBlock, hm, hmem, hn, hn4]
      · simp [TraceOK, AccessOK]
      · change Until H _ _ ((BContext.label [] 0 [] [.plain (.localGet 0)] C).fill
          ⟨st, ⟨[some (vI d), some (vI s), some (vI n), some (vI 0), some (vI 0), some (vI 0),
              some (vI (n % 4))], inst⟩,
            mpTail.map .plain⟩)
        have hr : n % 4 = n := Nat.mod_eq_of_lt hn4
        simpa only [hr, Nat.add_zero] using
          mp_tail_until H C st inst ma mem d s 0 n (vI n) (vI 0) (vI 0) hm hmem
            (by omega) (by omega) hsize (by omega)
    · wasm_eval 15 [block_simp, mpForward, mpBlock, hm, hmem, hn, hn4]
      · simp [TraceOK, AccessOK]
      · let C1 := BContext.label [] 0 [] [.plain (.localGet 0)] C
        let C2 := BContext.label [] 0 [] (mpTail.map .plain) C1
        change Until H _ _ (C2.fill
          ⟨st, ⟨[some (vI d), some (vI s), some (vI (4 * (n / 4))), some (vI 0), some (vI 0),
              some (vI 0), some (vI (n % 4))], inst⟩,
            [.plain (.loop .empty mp4)] ++ [.plain (.localGet 6), .plain (.itestEqz .w32),
              .plain (.brIf 1)]⟩)
        apply (mp4_until H C2 st inst ma mem d s 0 (4 * (n / 4)) (n % 4) (n / 4)
          (vI 0) (vI 0) [.plain (.localGet 6), .plain (.itestEqz .w32), .plain (.brIf 1)]
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
            ([.label 0 [] [.plain (.localGet 6), .plain (.itestEqz .w32), .plain (.brIf 1)]] ++
              mpTail.map .plain), .plain (.localGet 0)]⟩)
          wasm_eval 5 [block_simp, hr]
          · simp [TraceOK, AccessOK]
          · apply Until.done
            have he : 4 * (n / 4) = n := by omega
            refine ⟨vI (4 * (n / 4)), vI (d + 4 * (n / 4) - 4), vI (4 * (n / 4)),
              vI (s + 4 * (n / 4) - 4), vI 0, ?_⟩
            simp only [Nat.add_zero, he]
            rfl
        · change Until H _ _ (C1.fill ⟨_, _,
            [.label 0 [] [.plain (.localGet 6), .plain (.itestEqz .w32), .plain (.brIf 1)]] ++
              mpTail.map .plain⟩)
          wasm_eval 4 [block_simp, hr]
          · simp [TraceOK, AccessOK]
          · have ht := mp_tail_until H C (st.setMem ma (fwdCopy mem d s (4 * (n / 4))))
              inst ma (fwdCopy mem d s (4 * (n / 4))) d s (4 * (n / 4)) (n % 4)
              (vI (4 * (n / 4))) (vI (d + 4 * (n / 4) - 4))
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

end Subjects.Lz4C.Eval
