import FVATest.Subjects.Lz4C.Eval.Backward2
import FVATest.Subjects.Lz4C.Eval.ForwardBody2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def MvPost (C : BContext) (st : Store) (inst : ModuleInst) (d : Nat) (c : Config) : Prop :=
  ∃ u1 u2 u3 u4 u5 u6 : Val,
    c = C.fill ⟨st, ⟨[vI d, u1, u2, u3, u4, u5, u6], inst⟩, vals [vI d]⟩

/-- The backward path after its high-byte remainder. -/
theorem mb_rest_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s n : Nat) (u4 u5 u6 : Val)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + n ≤ mem.size) (hs : s + n ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (Span ma s n) (Span ma d n))
      (MvPost C (st.setMem ma (backCopy mem d s (4 * (n / 4)))) inst d)
      (C.fill ⟨st, ⟨[vI d, vI s, vI n, vI (4 * (n / 4)), u4, u5, u6], inst⟩,
        [.label 0 [] (.label 0 [] ((mbInner.drop 10).map .plain) :: mpForward.map .plain),
          .plain (.localGet 0)]⟩) := by
  by_cases hn4 : n < 4
  · wasm_eval 5 [block_simp, mbInner, hn4]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      have he : 4 * (n / 4) = 0 := by omega
      refine ⟨vI s, vI n, vI (4 * (n / 4)), u4, u5, u6, ?_⟩
      simp only [he, backCopy, setMem_self hmem]
      rfl
  · wasm_eval 9 [block_simp, mbInner, hn4]
    · simp [TraceOK, AccessOK]
    · let C1 := BContext.label [] 0 [] [.plain (.localGet 0)] C
      let C2 := BContext.label [] 0 [] (mpForward.map .plain) C1
      change Until H _ _ (C2.fill ⟨st,
        ⟨[vI d, .i32 (BitVec.ofNat 32 d - BitVec.ofNat 32 4), vI n, vI (4 * (n / 4)), u4, u5,
          .i32 (BitVec.ofNat 32 s - BitVec.ofNat 32 4)], inst⟩, [.plain (.loop .empty mb4)]⟩)
      apply (mb4_until H C2 st inst ma mem d s (n / 4) (vI n) u4 u5
        (BitVec.ofNat 32 d - BitVec.ofNat 32 4) (BitVec.ofNat 32 s - BitVec.ofNat 32 4) [] hm hmem
        (by omega) (by omega) hsize (by omega)
        (fun j hj => base_sub d j 4 (by decide) (by omega))
        (fun j hj => base_sub s j 4 (by decide) (by omega))).mono
        (fun c hc => ⟨fun m a ha => by
          obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a ha
          exact ⟨rfl, hlo, by omega⟩,
        fun m a ha => by
          obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a ha
          exact ⟨rfl, hlo, by omega⟩⟩) (fun _ hx => hx) |>.trans
      intro c hc
      subst c
      change Until H _ _ (C.fill ⟨_, _,
        [.label 0 [] (.label 0 [] [.label 0 [.loop .empty mb4] [.plain (.br 2)]] ::
          mpForward.map .plain), .plain (.localGet 0)]⟩)
      wasm_eval 2 [block_simp]
      · simp [TraceOK, AccessOK]
      · exact .done ⟨_, _, _, _, _, _, rfl⟩

/-- The backward path from the comparison's fall-through. -/
theorem mb_path_until (H : HostSem) (C : BContext) (st : Store) (inst : ModuleInst) (ma : Nat)
    (mem : MemInst) (d s n : Nat)
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + n ≤ mem.size) (hs : s + n ≤ mem.size) (hsize : mem.size < 2 ^ 32) :
    Until H (Within (Span ma s n) (Span ma d n))
      (MvPost C (st.setMem ma (backCopy mem d s n)) inst d)
      (C.fill ⟨st, ⟨[vI d, vI s, vI n, vI 0, vI 0, vI 0, vI 0], inst⟩,
        [.label 0 [] (.label 0 [] ((mbInner.drop 4).map .plain) :: mpForward.map .plain),
          .plain (.localGet 0)]⟩) := by
  by_cases hn : n = 0
  · subst n
    wasm_eval 5 [block_simp, mbInner]
    · simp [TraceOK, AccessOK]
    · apply Until.done
      refine ⟨vI s, vI 0, vI 0, vI 0, vI 0, vI 0, ?_⟩
      simp only [backCopy, setMem_self hmem]
      rfl
  · by_cases hr : n % 4 = 0
    · wasm_eval 13 [block_simp, mbInner, mbRem, hn, hr]
      · simp [TraceOK, AccessOK]
      · have he : 4 * (n / 4) = n := by omega
        simpa only [he, mbInner, List.drop_succ_cons, List.drop_zero, List.map_cons,
          List.map_nil] using
          mb_rest_until H C st inst ma mem d s n (vI 0) (vI 0) (vI 0) hm hmem hd hs hsize
    · wasm_eval 20 [block_simp, mbInner, mbRem, hn, hr, hm, hmem]
      · simp [TraceOK, AccessOK]
      · let C1 := BContext.label [] 0 [] [.plain (.localGet 0)] C
        let C2 := BContext.label [] 0 [] (mpForward.map .plain) C1
        let C3 := BContext.label [] 0 [] ((mbInner.drop 10).map .plain) C2
        change Until H _ _ (C3.fill ⟨st,
          ⟨[vI d, vI s, vI n, vI n, vI (n % 4), .i32 (BitVec.ofNat 32 s - BitVec.ofNat 32 1),
            .i32 (BitVec.ofNat 32 d - BitVec.ofNat 32 1)], inst⟩, [.plain (.loop .empty mb1)]⟩)
        have hdecomp : 4 * (n / 4) + n % 4 = n := by omega
        have hpre := (mb1_until H C3 st inst ma mem d s (4 * (n / 4)) (n % 4)
          (vI d) (vI s) (vI n) (BitVec.ofNat 32 d - BitVec.ofNat 32 1)
          (BitVec.ofNat 32 s - BitVec.ofNat 32 1) [] hm hmem (by omega) (by omega) hsize
          (by omega) (fun j hj => base_sub d j 1 (by decide) (by omega))
          (fun j hj => base_sub s j 1 (by decide) (by omega))).mono
          (P' := Within (Span ma s n) (Span ma d n))
          (fun c hc => ⟨fun m a ha => by
            obtain ⟨rfl, hlo, hhi⟩ := hc.1 m a ha
            exact ⟨rfl, by omega, by omega⟩,
          fun m a ha => by
            obtain ⟨rfl, hlo, hhi⟩ := hc.2 m a ha
            exact ⟨rfl, by omega, by omega⟩⟩) (fun _ hx => hx)
        refine Until.trans (by simpa only [hdecomp, List.append_nil] using hpre) ?_
        intro c hc
        subst c
        change Until H _ _ (C2.fill ⟨_, _,
          .label 0 [] [] :: (mbInner.drop 10).map .plain⟩)
        wasm_eval 1 [block_simp]
        · simp [TraceOK, AccessOK]
        · have hrest := mb_rest_until H C
            (st.setMem ma (backCopy mem (d + 4 * (n / 4)) (s + 4 * (n / 4)) (n % 4)))
            inst ma (backCopy mem (d + 4 * (n / 4)) (s + 4 * (n / 4)) (n % 4)) d s n
            (vI 0) (.i32 (BitVec.ofNat 32 s - BitVec.ofNat 32 1)
              ) (.i32 (BitVec.ofNat 32 d - BitVec.ofNat 32 1)) hm (setMem_get hmem _)
            (by simpa only [backCopy_size] using hd) (by simpa only [backCopy_size] using hs)
            (by simpa only [backCopy_size] using hsize)
          apply hrest.mono (fun _ hx => hx)
          intro c hc
          simpa only [MvPost, setMem_setMem, ← backCopy_add,
            show n % 4 + 4 * (n / 4) = n by omega] using hc

end Subjects.Lz4C.Eval
