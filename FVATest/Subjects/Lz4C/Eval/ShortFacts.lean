import FVATest.Subjects.Lz4C.Eval.ShortCode
import Mathlib.Tactic.IntervalCases

namespace Subjects.Lz4C.Eval

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option linter.unusedSimpArgs false

theorem head_decompose {ls : List Val} {src dst n cap op ip : Nat}
    (h : HeadLocals ls src dst n cap op ip) :
    ∃ u2 u15 u16 u17 u18 : Val,
      ls = [vI src, vI dst, u2, vI op, vI ip, vI (dst + cap), vI (dst + cap - 32),
        vI (src + n), vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7),
        vI (src + n - 4), vI (src + n - 8), vI (dst + cap - 12), vI (src + n - 15),
        u15, u16, u17, u18] := by
  rcases h with ⟨hlen, h0, h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have get (i : Nat) (hi : i < 19) : ls[i]? = some (ls[i]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  refine ⟨ls[2]'(by omega), ls[15]'(by omega), ls[16]'(by omega),
    ls[17]'(by omega), ls[18]'(by omega), List.ext_getElem? (fun i => ?_)⟩
  by_cases hi : i < 19
  · interval_cases i <;> simp_all only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      get 2 (by decide), get 15 (by decide), get 16 (by decide), get 17 (by decide), get 18
        (by decide)]
  · rw [List.getElem?_eq_none (by omega)]
    symm
    exact List.getElem?_eq_none (by simp; omega)

def tokenLs (src dst n cap op ip t ll : Nat) (u17 u18 : Val) : List Val :=
  [vI src, vI dst, vI ll, vI op, vI ip, vI (dst + cap), vI (dst + cap - 32),
    vI (src + n), vI (src + n - 16), vI (dst + cap - 5), vI (dst + cap - 7),
    vI (src + n - 4), vI (src + n - 8), vI (dst + cap - 12), vI (src + n - 15),
    vI (ip + 1), vI t, u17, u18]

def matchLs (src dst n cap op ip t off : Nat) : List Val :=
  [vI src, vI dst, vI (op + t / 16 - off), vI (ip + 1 + t / 16), vI (ip + 3 + t / 16),
    vI (dst + cap), vI (dst + cap - 32), vI (src + n), vI (src + n - 16),
    vI (dst + cap - 5), vI (dst + cap - 7), vI (src + n - 4), vI (src + n - 8),
    vI (dst + cap - 12), vI (src + n - 15), vI (t % 16), vI t, vI (op + t / 16), vI off]

noncomputable def shortCtx (C : Context) : Context :=
  .label 0 [] (shortRest8.map .plain) (ctx8 C)

theorem fwdCopy_outside (mem : MemInst) (d s n a : Nat) (ha : a < d ∨ d + n ≤ a) :
    (fwdCopy mem d s n).byte a = mem.byte a := by
  induction n generalizing mem d s with
  | zero => rfl
  | succ n ih =>
    rw [fwdCopy, ih _ _ _ (by omega), write_byte_one]
    simp only [show a ≠ d by omega, ite_false]

theorem copy_source_byte (mem : MemInst) (src dst n cap d s k a : Nat)
    (hsep : src + n ≤ dst ∨ dst + cap ≤ src) (hd : dst ≤ d) (hend : d + k ≤ dst + cap)
    (hlo : src ≤ a) (hhi : a < src + n) : (fwdCopy mem d s k).byte a = mem.byte a :=
  fwdCopy_outside mem d s k a (by omega)

theorem read_two (mem : MemInst) (p : Nat) :
    mem.read p 2 = (mem.byte p).toNat + 256 * (mem.byte (p + 1)).toNat := by
  simp [MemInst.read]

theorem short_copy (H : HostSem) (C : Context) (st : Store) (inst : ModuleInst) (ls : List Val)
    (a ma : Nat) (mem : MemInst) (src dst n cap d s k : Nat) (rest : List AInstr)
    (hcall : inst.funcs[3]? = some a)
    (hfun : st.funcs[a]? = some (.wasm copyType inst Lifted.func3))
    (hm : inst.mems[0]? = some ma) (hmem : st.mems[ma]? = some mem)
    (hd : d + k ≤ mem.size) (hs : s + k ≤ mem.size) (hsize : mem.size < 2 ^ 32)
    (hr : (src ≤ s ∧ s + k ≤ src + n) ∨ (dst ≤ s ∧ s + k ≤ dst + cap))
    (hw : dst ≤ d ∧ d + k ≤ dst + cap) :
    Until H
      (Within (fun m x => m = ma ∧ (Span ma src n m x ∨ Span ma dst cap m x)) (Span ma dst cap))
      (fun c => c = C.fill ⟨st.setMem ma (fwdCopy mem d s k), ⟨ls, inst⟩, vals [vI d] ++ rest⟩)
      (C.fill ⟨st, ⟨ls, inst⟩, vals [vI d, vI s, vI k] ++ [.plain (.call 3)] ++ rest⟩) := by
  apply (s1 H C st ⟨ls, inst⟩ [] rest a ma inst mem d s k hcall hfun hm hmem hd hs hsize).mono
  · intro c hc
    refine ⟨fun m x hx => ?_, fun m x hx => ?_⟩
    · obtain ⟨rfl, hlo, hhi⟩ := hc.1 m x hx
      refine ⟨rfl, ?_⟩
      rcases hr with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact .inl ⟨rfl, by omega, by omega⟩
      · exact .inr ⟨rfl, by omega, by omega⟩
    · obtain ⟨rfl, hlo, hhi⟩ := hc.2 m x hx
      exact ⟨rfl, by omega, by omega⟩
  · exact fun _ hx => hx

end Subjects.Lz4C.Eval
