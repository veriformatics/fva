import FVATest.Subjects.Lz4C.Eval.Forward2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Copy the high `r` bytes backwards; `i` bytes remain for the four-byte loop. -/
theorem mb1_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s i r : Nat) (u0 u1 u2 : Val) (bd bs : BitVec 32) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + i + r ≤ mem.size) (hs : s + i + r ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (hr : 0 < r)
    (hbd : ∀ j, 0 < j → iadd bd (BitVec.ofNat 32 j) = BitVec.ofNat 32 (d + j - 1))
    (hbs : ∀ j, 0 < j → iadd bs (BitVec.ofNat 32 j) = BitVec.ofNat 32 (s + j - 1)) :
    Until H (Within (Span ma (s + i) r) (Span ma (d + i) r))
      (fun c => c = C.fill ⟨st.setMem ma (backCopy mem (d + i) (s + i) r),
        ⟨[some u0, some u1, some u2, some (vI i), some (vI 0), some (.i32 bs), some (.i32 bd)],
            inst⟩, rest⟩)
      (C.fill ⟨st,
        ⟨[some u0, some u1, some u2, some (vI (i + r)), some (vI r), some (.i32 bs),
            some (.i32 bd)], inst⟩,
        [.plain (.loop .empty mb1)] ++ rest⟩) := by
  induction r generalizing st mem with
  | zero => omega
  | succ r ih =>
    have hd1 : d + (i + (r + 1)) - 1 = d + i + r := by omega
    have hs1 : s + (i + (r + 1)) - 1 = s + i + r := by omega
    have hi1 : i + (r + 1) - 1 = i + r := by omega
    by_cases hz : r = 0
    · subst r
      wasm_eval 18 [block_simp, mb1, hm, hmem, hbd, hbs, hd1, hs1, hi1]
      · simp [TraceOK, AccessOK, Span]
        constructor <;> intro a hlo hhi <;> constructor <;> omega
      · apply Until.done
        simp only [backCopy, Nat.add_zero]
    · wasm_eval 18 [block_simp, mb1, hm, hmem, hbd, hbs, hd1, hs1, hi1, Nat.add_sub_cancel]
      · simp [TraceOK, AccessOK, Span]
        constructor <;> intro a hlo hhi <;> constructor <;> omega
      · have hi := ih (st.setMem ma (mem.write (d + i + r) 1 (mem.byte (s + i + r)).toNat))
          (mem.write (d + i + r) 1 (mem.byte (s + i + r)).toNat)
          (setMem_get hmem _) (by simp only [write_size]; omega)
          (by simp only [write_size]; omega) (by simpa only [write_size] using hsize) (by omega)
        apply hi.mono
        · intro c hc
          refine ⟨fun m a h => ?_, fun m a h => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a h
            exact ⟨rfl, hlo, by omega⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a h
            exact ⟨rfl, hlo, by omega⟩
        · intro c hc
          simpa only [backCopy, setMem_setMem] using hc

/-- Backward four-byte groups; the final `br 2` remains for the caller's labels. -/
theorem mb4_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s k : Nat) (u2 u4 u5 : Val) (bd bs : BitVec 32) (rest : List AInstr)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + 4 * k ≤ mem.size) (hs : s + 4 * k ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (hk : 0 < k)
    (hbd : ∀ j, 4 ≤ j → iadd bd (BitVec.ofNat 32 j) = BitVec.ofNat 32 (d + j - 4))
    (hbs : ∀ j, 4 ≤ j → iadd bs (BitVec.ofNat 32 j) = BitVec.ofNat 32 (s + j - 4)) :
    Until H (Within (Span ma s (4 * k)) (Span ma d (4 * k)))
      (fun c => c = C.fill ⟨st.setMem ma (backCopy mem d s (4 * k)),
        ⟨[some (vI d), some (.i32 bd), some u2, some (vI 0), some (vI d), some (vI s),
            some (.i32 bs)], inst⟩,
        [.label 0 [.loop .empty mb4] [.plain (.br 2)]] ++ rest⟩)
      (C.fill ⟨st,
        ⟨[some (vI d), some (.i32 bd), some u2, some (vI (4 * k)), some u4, some u5,
            some (.i32 bs)], inst⟩,
        [.plain (.loop .empty mb4)] ++ rest⟩) := by
  induction k generalizing st mem u4 u5 with
  | zero => omega
  | succ k ih =>
    have hd0 : d + 4 * (k + 1) - 4 = d + 4 * k := by omega
    have hs0 : s + 4 * (k + 1) - 4 = s + 4 * k := by omega
    have hk0 : 4 * (k + 1) - 4 = 4 * k := by omega
    have hb0 : ¬ mem.size < s + 4 * k + 1 := by omega
    have hb1 : ¬ mem.size < s + 4 * k + 1 + 1 := by omega
    have hb2 : ¬ mem.size < s + 4 * k + 2 + 1 := by omega
    have hb3 : ¬ mem.size < s + 4 * k + 3 + 1 := by omega
    have hw0 : ¬ mem.size < d + 4 * k + 1 := by omega
    have hw1 : ¬ mem.size < d + 4 * k + 1 + 1 := by omega
    have hw2 : ¬ mem.size < d + 4 * k + 2 + 1 := by omega
    have hw3 : ¬ mem.size < d + 4 * k + 3 + 1 := by omega
    by_cases hz : k = 0
    · subst k
      wasm_eval 36 [block_simp, mb4, hm, hmem, hbd, hbs, hd0, hs0, hk0,
        hb0, hb1, hb2, hb3, hw0, hw1, hw2, hw3]
      · simp [TraceOK, AccessOK, Span]
        repeat' constructor
        all_goals intro a hlo hhi
        all_goals constructor <;> omega
      · apply Until.done
        rfl
    · wasm_eval 37 [block_simp, mb4, hm, hmem, hbd, hbs, hd0, hs0, hk0,
        hb0, hb1, hb2, hb3, hw0, hw1, hw2, hw3]
      · simp [TraceOK, AccessOK, Span]
        repeat' constructor
        all_goals intro a hlo hhi
        all_goals constructor <;> omega
      · have hi := ih (st.setMem ma (backCopy mem (d + 4 * k) (s + 4 * k) 4))
          (backCopy mem (d + 4 * k) (s + 4 * k) 4) (vI (d + 4 * k)) (vI (s + 4 * k))
          (setMem_get hmem _) (by simp only [backCopy_size]; omega)
          (by simp only [backCopy_size]; omega) (by simpa only [backCopy_size] using hsize)
            (by omega)
        apply hi.mono
        · intro c hc
          refine ⟨fun m a h => ?_, fun m a h => ?_⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a h
            exact ⟨rfl, hlo, by omega⟩
          · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a h
            exact ⟨rfl, hlo, by omega⟩
        · intro c hc
          rw [setMem_setMem] at hc
          have hm4 := backCopy_add mem d s 4 (4 * k)
          rw [← hm4] at hc
          simpa only [show 4 * (k + 1) = 4 + 4 * k by omega] using hc

end Subjects.Lz4C.Eval
