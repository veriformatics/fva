import FVATest.Subjects.EdgerCpm.BodyFreeSupport

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem cleanup_returns (W : World) (t b : BitVec 32) (s : Store) (j : Nat)
    (p last : BitVec 32) (hstate : LoopState W t b W.x.n s) :
    Must W.H (post W) (bodyContext.fill
      ⟨s, mainFrame W.x W.l W.inst t W.x.n j p last,
        .plain rowLoop :: (processCode.drop 17).map .plain⟩) := by
  obtain ⟨hm, a160, a207, a12, a13, hi207, hi12, hi13, hex, f160, f207, f12, f13⟩ :=
    hstate.linked
  obtain ⟨mem, hmem, hts, hbs⟩ := hstate.scratch.room
  have hread := read32 hmem hstate.table
  have hbound : ¬ mem.size < t.toNat + 4 := by omega
  have hrow : ieq (BitVec.ofNat 32 W.x.n) (.ofNat 32 W.x.n) = 1 := by simp [ieq, Num.bool]
  have hzero : ieq (0 : BitVec 32) (.ofNat 32 1) = 0 := by decide
  have hsh : ishl (0 : BitVec 32) (.ofNat 32 2) = 0 := by decide
  have hadd : iadd t (0 : BitVec 32) = t := by simp [iadd_eq]
  have hone : (1 : BitVec 32) ≠ 0 := by decide
  have hinc : iadd (0 : BitVec 32) (.ofNat 32 1) = 1 := by decide
  have heq1 : ieq (1 : BitVec 32) (.ofNat 32 1) = 1 := by decide
  have hneq : t.toNat ≠ b.toNat := by
    have := hstate.scratch.disjoint
    have := W.domain.2.1
    omega
  have htfresh : ¬ InBlocks (W.blocks W.initial) t.toNat :=
    (hstate.scratch.tablePrivate _ (le_refl _) (by omega)).2
  have hbfresh : ¬ InBlocks (W.blocks W.initial) b.toNat :=
    (hstate.scratch.bufferPrivate _ (le_refl _) (by have := W.domain.2.1; omega)).2
  have hold : PositiveOld (W.blocks W.initial) (W.blocks s) :=
    fun q hq _ => hstate.scratch.old q hq
  simp only [bodyContext, Context.fill, mainFrame]
  wasm_run [rowLoop, processCode, outerCode, outerLoop, blockCode, loopCode, thenCode,
    Lifted.func86, List.getD, List.drop_succ_cons, List.drop_zero, hm, hmem, hbound,
    hread, hrow, hzero, hsh, hadd, hone, hi13, f13, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, Nat.add_zero]
  apply must_free W.allocator hstate.scratch.next hstate.scratch.buffer f13
  · simp [seqFocus, atFocus, HostAt, toVal_instr, toVal_frame, toVal_label, toVal_invoke]
  · intro s₁ hf₁
    have hcaller₁ := hf₁.caller hold hbfresh W.callerSafe
    have hold₁ := hf₁.positive hold hbfresh
    have hcells₁ := cells_same (same_mono hcaller₁ (fun a ha => Or.inr ha)) hstate.cells
    have hkept₁ := same_trans hstate.kept (same_mono hcaller₁ (fun a ha => Or.inl ha))
    have htmember := hf₁.old (t.toNat, 4) hstate.scratch.table hneq
    have htable₁ : Holds s₁ t.toNat (le32 b) := by
      apply holds_same (same_mono hf₁.same (Q := fun a => t.toNat ≤ a ∧ a < t.toNat + 4)
        (fun a ha => Or.inr ⟨(t.toNat, 4), by
          simp only [List.mem_filter, decide_eq_true_iff]
          exact ⟨hstate.scratch.table, hneq⟩, ha⟩)) hstate.table
      intro a ha hb
      simpa [le32] using And.intro ha hb
    obtain ⟨mem₁, hmem₁, htfit, -⟩ := htable₁
    have htfit' : t.toNat + 4 ≤ mem₁.size := by simpa [le32] using htfit
    have hbound₁ : ¬ mem₁.size < t.toNat + 4 := by omega
    let s₂ := put s₁ mem₁ t.toNat 4 0
    have hframe : W.blocks s₂ = W.blocks s₁ ∧ W.ready 0 s₂ :=
      put_frame W.allocator hf₁.next hmem₁ (fun a ha hb =>
        Or.inr ⟨(t.toNat, 4), htmember, ha, hb⟩)
    have hold₂ : PositiveOld (W.blocks W.initial) (W.blocks s₂) := by
      simpa only [hframe.1] using hold₁
    have htmember₂ : (t.toNat, 4) ∈ W.blocks s₂ := by
      simpa only [hframe.1] using htmember
    have hcaller₂ : SameOn s₁ s₂ (fun a => W.l.kept W.x a ∨ W.l.counts W.x a) := by
      apply same_put hmem₁
      intro a ha hz
      obtain ⟨hheap, hfresh⟩ := hstate.scratch.tablePrivate a hz.1 hz.2
      exact (W.callerSafe a ha).elim (fun hn => hn hheap) hfresh
    have hcells₂ := cells_same (same_mono hcaller₂ (fun a ha => Or.inr ha)) hcells₁
    have hkept₂ := same_trans hkept₁ (same_mono hcaller₂ (fun a ha => Or.inl ha))
    have f13₁ : s₁.funcs[a13]? = some (.host ⟨[.num .i32], []⟩ W.free) := by
      obtain ⟨fi, hfi, rfl⟩ := hf₁.ext.1 a13 _ f13
      exact hfi
    have f13₂ : s₂.funcs[a13]? = some (.host ⟨[.num .i32], []⟩ W.free) := f13₁
    simp only [seqPlug, atPlug, wasm_step, vals]
    wasm_run [hm, hmem₁, hbound₁, hinc, heq1, hone, hi13, f13₁, f13₂, Val.numBits,
      Nat.add_zero, show (0#32 : BitVec 32).toNat = 0 from rfl]
    apply must_free W.allocator hframe.2 htmember₂ f13₂
    · simp [seqFocus, atFocus, HostAt, toVal_instr, toVal_frame, toVal_label, toVal_invoke]
    · intro s₃ hf₃
      have hcaller₃ := hf₃.caller hold₂ htfresh W.callerSafe
      have hcells₃ := cells_same (same_mono hcaller₃ (fun a ha => Or.inr ha)) hcells₂
      have hkept₃ := same_trans hkept₂ (same_mono hcaller₃ (fun a ha => Or.inl ha))
      simp only [seqPlug, atPlug, wasm_step, vals]
      wasm_run []
      refine Must.done (o := .returned s₃ []) ⟨rfl, rfl⟩ ?_
      exact ⟨rfl, fun i hi j hj => (hcells₃ i hi j hj).1 (Or.inl hi), hkept₃⟩

end Subjects.EdgerCpm.Body
