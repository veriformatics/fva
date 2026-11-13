import FVATest.Subjects.Lz4C.Eval.S2

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def wcBody (dl sl el : Nat) (tail : List Instr) : List Instr :=
  [.localGet dl, .localGet sl, .iconst .w32 8, .call 3, .drop,
    .localGet sl, .iconst .w32 8, .ibinop .w32 .add, .localSet sl,
    .localGet dl, .iconst .w32 8, .ibinop .w32 .add, .localTee dl,
    .localGet el, .irelop .w32 (.lt .u), .brIf 0] ++ tail

def wcLoop (dl sl el : Nat) (tail : List Instr) : Instr := .loop .empty (wcBody dl sl el tail)

theorem local_pair_reset (ls : List (Option Val)) (dl sl : Nat) (a b c d : Option Val)
    (hne : dl ≠ sl) :
    ((((ls.set sl a).set dl b).set dl c).set sl d) = (ls.set dl c).set sl d := by
  rw [List.set_set, List.set_comm a c (Ne.symm hne), List.set_set]

/-- One callee summary per iteration; the caller owns the terminal label's tail. -/
theorem wc_until (H : HostSem) (C : Context) (st : Store) (inst : ModuleInst)
    (ls : List (Option Val))
    (a ma : Nat) (mem : MemInst) (dl sl el q m e k : Nat) (tail : List Instr)
    (rest : List AInstr) (hds : dl ≠ sl) (hde : dl ≠ el) (hse : sl ≠ el)
    (hdl : ls[dl]? = some (some (vI q))) (hsl : ls[sl]? = some (some (vI m)))
        (hel : ls[el]? = some (some (vI e)))
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : q + 8 * k ≤ mem.size) (hs : m + 8 * k ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (hk : 0 < k) (hend : e ≤ q + 8 * k) (hprev : k = 1 ∨ q + 8 * (k - 1) < e) :
    Until H (Within (Span ma m (8 * k)) (Span ma q (8 * k)))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem q m (8 * k)),
        ⟨(ls.set dl (some (vI (q + 8 * k)))).set sl (some (vI (m + 8 * k))), inst⟩,
        [.label 0 [wcLoop dl sl el tail] (tail.map .plain)] ++ rest⟩)
      (C.fill ⟨st, ⟨ls, inst⟩, [.plain (wcLoop dl sl el tail)] ++ rest⟩) := by
  induction k generalizing st ls mem q m with
  | zero => omega
  | succ k ih =>
    have hld : dl < ls.length := (List.getElem?_eq_some_iff.mp hdl).1
    have hls : sl < ls.length := (List.getElem?_eq_some_iff.mp hsl).1
    wasm_eval 3 [block_simp, wcLoop, wcBody, hdl, hsl]
    · simp [TraceOK, AccessOK]
    · have hc := s1 H (Context.label 0 [wcLoop dl sl el tail] rest C) st ⟨ls, inst⟩ []
        ((wcBody dl sl el tail).drop 4 |>.map .plain) a ma inst mem q m 8 hcall hfun hm hmem
        (by omega) (by omega) hsize
      refine Until.trans (hc.mono
        (fun c hw => ⟨fun mm x hx => by
          obtain ⟨rfl, hlo, hhi⟩ := hw.1 mm x hx
          exact ⟨rfl, hlo, by omega⟩,
        fun mm x hx => by
          obtain ⟨rfl, hlo, hhi⟩ := hw.2 mm x hx
          exact ⟨rfl, hlo, by omega⟩⟩) (fun _ hx => hx)) ?_
      intro c hc
      subst c
      change Until H _ _ (C.fill ⟨_, ⟨ls, inst⟩,
        [.label 0 [wcLoop dl sl el tail]
          (vals [vI q] ++ ((wcBody dl sl el tail).drop 4).map .plain)] ++ rest⟩)
      by_cases hz : k = 0
      · subst k
        wasm_eval 11 [block_simp, wcBody, wcLoop, hdl, hsl, hel,
          List.getElem?_set_self, List.getElem?_set_ne]
        · simp [TraceOK, AccessOK]
        · apply Until.done
          rw [List.set_comm (some (vI (m + 8))) (some (vI (q + 8))) (Ne.symm hds)]
          rfl
      · wasm_eval 12 [block_simp, wcBody, wcLoop, hdl, hsl, hel,
          List.getElem?_set_self, List.getElem?_set_ne]
        · simp [TraceOK, AccessOK]
        · let ls' := (ls.set sl (some (vI (m + 8)))).set dl (some (vI (q + 8)))
          have hd' : ls'[dl]? = some (some (vI (q + 8))) := by
            exact List.getElem?_set_self (by simpa only [List.length_set] using hld)
          have hs' : ls'[sl]? = some (some (vI (m + 8))) := by
            simp only [ls', List.getElem?_set_ne hds, List.getElem?_set_self hls]
          have he' : ls'[el]? = some (some (vI e)) := by
            simpa only [ls', List.getElem?_set_ne hde, List.getElem?_set_ne hse] using hel
          have hi := ih (st.setMem ma (fwdCopy mem q m 8)) ls' (fwdCopy mem q m 8)
            (q + 8) (m + 8) hd' hs' he' (by simpa only [setMem_funcs] using hfun)
            (setMem_get hmem _) (by simp only [fwdCopy_size]; omega)
            (by simp only [fwdCopy_size]; omega) (by simpa only [fwdCopy_size] using hsize)
            (by omega) (by omega) (by omega)
          apply hi.mono
          · intro c hw
            refine ⟨fun mm x hx => ?_, fun mm x hx => ?_⟩
            · obtain ⟨rfl, hlo, hhi⟩ := hw.1 mm x hx
              exact ⟨rfl, by omega, by omega⟩
            · obtain ⟨rfl, hlo, hhi⟩ := hw.2 mm x hx
              exact ⟨rfl, by omega, by omega⟩
          · intro c hc
            simp only [ls', setMem_setMem, local_pair_reset _ _ _ _ _ _ _ hds] at hc
            have hm8 := fwdCopy_add mem q m 8 (8 * k)
            rw [← hm8] at hc
            simpa only [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.add_assoc] using hc

theorem chunks_spec {q e : Nat} (hqe : q ≤ e) :
    0 < chunks q e ∧ e ≤ q + 8 * chunks q e ∧
      (chunks q e = 1 ∨ q + 8 * (chunks q e - 1) < e) := by
  unfold chunks
  omega

end Subjects.Lz4C.Eval
