import FVATest.Subjects.Lz4C.Eval.Code2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- The byte tail, with every caller label and operand stack preserved. -/
theorem mp1_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s r : Nat) (u0 u1 u2 u5 : Val) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + r ≤ mem.size) (hs : s + r ≤ mem.size) (hsize : mem.size < 2 ^ 32) (hr : 0 < r) :
    Until H (Within (Span ma s r) (Span ma d r))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem d s r),
        ⟨[some u0, some u1, some u2, some (vI (s + r)), some (vI (d + r)), some u5, some (vI 0)],
            inst⟩, rest⟩)
      (C.fill ⟨st,
          ⟨[some u0, some u1, some u2, some (vI s), some (vI d), some u5, some (vI r)], inst⟩,
        [.plain (.loop .empty mp1)] ++ rest⟩) := by
  induction r generalizing st mem d s with
  | zero => omega
  | succ r ih =>
    by_cases hz : r = 0
    · subst r
      wasm_eval 17 [block_simp, mp1, cp1, permInstr, permLocal, hm, hmem]
      · simp [TraceOK, AccessOK, Span]
        constructor <;> intro a hlo hhi <;> constructor <;> omega
      · exact .done rfl
    · wasm_eval 17 [block_simp, mp1, cp1, permInstr, permLocal, hm, hmem, Nat.add_sub_cancel]
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
theorem mp4_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s i e r k : Nat) (u3 u5 : Val) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + e ≤ mem.size) (hs : s + e ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (he : e = i + 4 * k) (hk : 0 < k) :
    Until H (Within (Span ma (s + i) (4 * k)) (Span ma (d + i) (4 * k)))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem (d + i) (s + i) (4 * k)),
        ⟨[some (vI d), some (vI s), some (vI e), some (vI (d + e - 4)), some (vI e),
            some (vI (s + e - 4)), some (vI r)], inst⟩, rest⟩)
      (C.fill ⟨st,
          ⟨[some (vI d), some (vI s), some (vI e), some u3, some (vI i), some u5, some (vI r)],
          inst⟩,
        [.plain (.loop .empty mp4)] ++ rest⟩) := by
  induction k generalizing st mem i u3 u5 with
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
      wasm_eval 39 [block_simp, mp4, cp4, permInstr, permLocal, hm, hmem, hb0, hb1, hb2, hb3,
        hw0, hw1, hw2, hw3]
      · simp [TraceOK, AccessOK, Span]
        repeat' constructor
        all_goals intro a hlo hhi
        all_goals constructor <;> omega
      · apply Until.done
        have he1 : i + 4 = e := by omega
        have hd1 : d + e - 4 = d + i := by omega
        have hs1 : s + e - 4 = s + i := by omega
        simp only [Nat.mul_one, he1, hd1, hs1]
    · wasm_eval 39 [block_simp, mp4, cp4, permInstr, permLocal, hm, hmem, hb0, hb1, hb2, hb3,
        hw0, hw1, hw2, hw3]
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

end Subjects.Lz4C.Eval
