import FVATest.Subjects.Lz4C.Loop
import FVATest.Subjects.Lz4C.Spec
import FVATest.Subjects.Lz4C.Instance
import FVA.Proof.Lib.Mem

/-!
# R1 from the cutpoint statements (contract U20)

The prepared fresh instance (`store0` + the source and destination bytes), the export lookup and
the entry code lead to the main loop (`Loop.lean`), so every call returns one `i32`, reading and
writing only R1's sets. Conditional on `Entry`, `ShortcutS5`, `SegA`…`SegD` and `ErrRet` (proof
support; outside the review surface).
-/

namespace Subjects.Lz4C.Top

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref Subjects.Lz4C

/-- Memory 0 of the fresh instance. -/
noncomputable def mem0 : MemInst := store0.mems.getD 0 ⟨0, none, fun _ => 0⟩

section
attribute [local irreducible] alloc

theorem store0_mem : store0.mems[0]? = some mem0 := by kernel_rfl
theorem mem0_size : mem0.size = 2097152 := by decide +kernel
theorem mem0_tables : TablesOK mem0 := by unfold TablesOK; decide +kernel
theorem inst_mem : alloc.2.mems[0]? = some 0 := by decide +kernel
theorem inst_export : alloc.2.exportFunc "LZ4_decompress_safe" = some 2 := by decide +kernel
theorem inst_f3 : alloc.2.funcs[3]? = some 3 := by decide +kernel
theorem inst_f4 : alloc.2.funcs[4]? = some 4 := by decide +kernel
theorem store0_f2 : store0.funcs[2]? = some (.wasm decType alloc.2 Lifted.func2) := by kernel_rfl
theorem store0_f3 : store0.funcs[3]? = some (.wasm copyType alloc.2 Lifted.func3) := by
  kernel_rfl
theorem store0_f4 : store0.funcs[4]? = some (.wasm copyType alloc.2 Lifted.func4) := by
  kernel_rfl

end

-- The kernel facts above carry the instance; elaboration below never unfolds its construction.
attribute [local irreducible] alloc initConfig store0 mem0

/-- The store after the caller wrote the source, then the destination bytes. -/
noncomputable def prepped (src dst : Nat) (input initDst : List UInt8) : Store :=
  (store0.withBytes src input).withBytes dst initDst

theorem prep_eq {src dst : Nat} {input initDst : List UInt8} (h1 : src + input.length ≤ 2097152)
    (h2 : dst + initDst.length ≤ 2097152) :
    store0.prep [.write src input, .write dst initDst] = some (prepped src dst input initDst) := by
  simp only [Store.prep, store0_mem, Store.withBytes_mem0 store0_mem, MemInst.withBytes_size,
    mem0_size, h1, h2, ↓reduceIte]
  rfl

theorem prepped_mem (src dst : Nat) (input initDst : List UInt8) :
    (prepped src dst input initDst).mems[0]? =
      some ((mem0.withBytes src input).withBytes dst initDst) :=
  Store.withBytes_mem0 (Store.withBytes_mem0 store0_mem _ _) _ _

theorem withBytes_low (mem : MemInst) {p a : Nat} (bs : List UInt8) (h : a < p) :
    (mem.withBytes p bs).byte a = mem.byte a := by
  simp only [MemInst.withBytes]
  exact ite_eq_right (by omega)

theorem good {src dst : Nat} {input initDst : List UInt8} (hs : 131072 ≤ src)
    (hs' : src + input.length ≤ 2097152) (hd : 131072 ≤ dst) (hd' : dst + initDst.length ≤ 2097152)
    (hj : src + input.length ≤ dst ∨ dst + initDst.length ≤ src) :
    Good (prepped src dst input initDst) alloc.2 0 src dst input.length initDst.length where
  a3 := ⟨3, inst_f3, store0_f3⟩
  a4 := ⟨4, inst_f4, store0_f4⟩
  ma0 := inst_mem
  mem := by
    refine ⟨_, prepped_mem src dst input initDst, mem0_size, mem0_tables.of_low fun a ha => ?_⟩
    rw [withBytes_low _ _ (by omega), withBytes_low _ _ (by omega)]
  srcLo := hs
  dstLo := hd
  srcHi := hs'
  dstHi := hd'
  disj := hj

/-- From the invocation, every execution reaches `func 2`'s return of one `i32`, inside R1's
sets. -/
theorem call_until (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC)
    (hD : SegD) (hR : ErrRet) {H : HostSem} {src dst : Nat} {input initDst : List UInt8}
    (hs : 131072 ≤ src) (hs' : src + input.length ≤ 2097152) (hd : 131072 ≤ dst)
    (hd' : dst + initDst.length ≤ 2097152)
    (hj : input = [] ∨ initDst = [] ∨ src + input.length ≤ dst ∨ dst + initDst.length ≤ src) :
    Until H (Within (R1R src input.length dst initDst.length) (R1W dst initDst.length))
      (fun c => ∃ st' v, c = ⟨st', ⟨[], {}⟩, vals [.i32 v]⟩)
      (invokeConfig (prepped src dst input initDst) 2
        [vI src, vI dst, vI input.length, vI initDst.length]) := by
  have he := hE H (prepped src dst input initDst) alloc.2 2 0 _ src dst input.length
    initDst.length store0_f2 inst_mem (prepped_mem src dst input initDst) (by omega) (by omega)
    (by omega) (by omega) (fun _ => by simp only [MemInst.withBytes_size, mem0_size]; omega)
  refine Until.trans (untilR1 he (fun m a h => Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2⟩)))
    fun _ _ h => h.elim) ?_
  rintro c (⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hc, hn, ls, hl, rfl⟩)
  · exact .done ⟨_, _, rfl⟩
  · refine .done ⟨prepped src dst input initDst,
      if ((mem0.withBytes src input).withBytes dst initDst).byte src = 0 then 0
      else BitVec.ofNat 32 4294967295, ?_⟩
    split <;> rfl
  · have hj' : src + input.length ≤ dst ∨ dst + initDst.length ≤ src := by
      rcases hj with h | h | h
      · exact absurd (congrArg List.length h) hn
      · exact absurd (congrArg List.length h) hc
      · exact h
    exact loop hS5 hA hB hC hD hR _ _ ls dst src rfl (good hs hs' hd hd' hj') hl (Nat.le_refl _)
      (by omega) (Nat.le_refl _) (by omega)

/-- R1 from the cutpoint statements. -/
theorem r1_of (hE : Entry) (hS5 : ShortcutS5) (hA : SegA) (hB : SegB) (hC : SegC) (hD : SegD)
    (hR : ErrRet) : r1 := by
  intro src dst input initDst hs hs' hd hd' _ _ hj
  refine ⟨fun H => ⟨_, _, store0, instance_store0 H, prep_eq hs' hd'⟩, ?_⟩
  rintro H s inst ⟨s₀, hi, hp⟩
  obtain ⟨rfl, rfl⟩ := instance_eq hi
  obtain rfl := Option.some.inj (hp.symm.trans (prep_eq hs' hd'))
  have hu := call_until hE hS5 hA hB hC hD hR (H := H) hs hs' hd hd' hj
  have hok : InvokeOK (prepped src dst input initDst) 2
      [vI src, vI dst, vI input.length, vI initDst.length] :=
    ⟨_, store0_f2, .cons trivial (.cons trivial (.cons trivial (.cons trivial .nil)))⟩
  refine ⟨⟨2, inst_export, hok, (mustW_of_until (Q := fun _ => True) hu ?_).2⟩,
    ⟨2, inst_export, hok, (mustW_of_until hu ?_).1⟩⟩
  · rintro c ⟨st', v, rfl⟩
    exact mustW_final (o := .returned st' [.i32 v]) ⟨rfl, rfl⟩ trivial
  · rintro c ⟨st', v, rfl⟩
    exact mustW_final (o := .returned st' [.i32 v]) ⟨rfl, rfl⟩ ⟨v, rfl⟩

end Subjects.Lz4C.Top
