import FVATest.Subjects.EdgerCpm.BodyColumn

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

structure World where
  x : Input
  l : Layout
  initial : Store
  inst : ModuleInst
  H : HostSem
  alloc : Nat
  free : Nat
  heap : Nat → Prop
  blocks : Store → List (Nat × Nat)
  ready : Nat → Store → Prop
  domain : Domain x
  allocator : Allocator H alloc free heap (8 * x.m) blocks ready
  callerSafe : ∀ a, l.kept x a ∨ l.counts x a → ¬ heap a ∨ InBlocks (blocks initial) a
  separated : ∀ a, l.kept x a → ¬ l.counts x a
  yBound : l.y + 16 ≤ 2 ^ 32
  libBound : l.lib + 32 ≤ 2 ^ 32
  dataBound : l.d + 8 * x.m ≤ 2 ^ 32
  countsBound : l.c + 8 * x.n * x.m ≤ 2 ^ 32

theorem World.n8 (W : World) : 8 * W.x.n < 2 ^ 32 := by
  have h := Nat.mul_le_mul_left (8 * W.x.n) (by have := W.domain.2.1; omega : 1 ≤ W.x.m)
  simp only [Nat.mul_one] at h
  have := W.domain.2.2
  omega

theorem World.n31 (W : World) : W.x.n < 2 ^ 31 := by have := W.n8; omega

theorem World.m31 (W : World) : W.x.m < 2 ^ 31 := by have := W.domain.2.2; omega

structure LoopState (W : World) (t b : BitVec 32) (r : Nat) (s : Store) : Prop where
  linked : Linked s W.inst W.alloc W.free
  scratch : Scratch W.heap W.blocks W.ready (W.blocks W.initial) W.x.m t b s
  library : LibData s W.x W.l
  table : Holds s t.toNat (le32 b)
  cells : Cells s W.x W.l r 0
  kept : SameOn W.initial s (W.l.kept W.x)

theorem scratch_changed {H : HostSem} {alloc free cap : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    {initial : List (Nat × Nat)} {m : Nat} {t b : BitVec 32} {s s' : Store} {P : Nat → Prop}
    (hA : Allocator H alloc free heap cap blocks ready)
    (h : Scratch heap blocks ready initial m t b s) (hc : Changed s s' P)
    (hP : ∀ a, heap a → ¬ InBlocks (blocks s) a → P a) :
    Scratch heap blocks ready initial m t b s' := by
  obtain ⟨hb, hr⟩ := changed_allocator hA hc h.next hP
  obtain ⟨before, after, hbefore, hafter, hs, hp, hx, he⟩ := hc
  obtain ⟨mem, hmem, hts, hbs⟩ := h.room
  have hm : mem = before := Option.some.inj (hmem.symm.trans hbefore)
  subst mem
  refine ⟨hr, by simpa only [hb] using h.old, by simpa only [hb] using h.table,
    by simpa only [hb] using h.buffer, h.tableBound, h.bufferBound, h.tablePrivate,
    h.bufferPrivate, h.disjoint, after, hafter, ?_, ?_⟩
  · simpa only [MemInst.size, hp] using hts
  · simpa only [MemInst.size, hp] using hbs

theorem linked_changed {s s' : Store} {inst : ModuleInst} {alloc free : Nat} {P : Nat → Prop}
    (h : Linked s inst alloc free) (hc : Changed s s' P) : Linked s' inst alloc free := by
  obtain ⟨_, _, _, _, rfl, _⟩ := hc
  exact h

theorem LoopState.outside_buffer {W : World} {t b : BitVec 32} {r : Nat} {s : Store}
    (h : LoopState W t b r s) {a : Nat} (ha : W.l.kept W.x a ∨ W.l.counts W.x a) :
    outsideBuffer b W.x.m a := by
  by_contra hn
  obtain ⟨hp, hi⟩ := h.scratch.bufferPrivate a (by unfold outsideBuffer at hn; omega)
    (by unfold outsideBuffer at hn; omega)
  exact (W.callerSafe a ha).elim (fun hx => hx hp) hi

theorem LoopState.table_not_counts {W : World} {t b : BitVec 32} {r : Nat} {s : Store}
    (h : LoopState W t b r s) {a : Nat} (ha : t.toNat ≤ a) (hb : a < t.toNat + 4) :
    ¬ W.l.counts W.x a := by
  intro hc
  obtain ⟨hp, hi⟩ := h.scratch.tablePrivate a ha hb
  exact (W.callerSafe a (Or.inr hc)).elim (fun hx => hx hp) hi

theorem LoopState.copy {W : World} {t b : BitVec 32} {r : Nat} {s s' : Store}
    (h : LoopState W t b r s) (hc : Changed s s' (outsideBuffer b W.x.m)) :
    LoopState W t b r s' := by
  have hkeep := same_mono (changed_same hc) (fun a ha => h.outside_buffer (Or.inl ha))
  refine ⟨linked_changed h.linked hc, scratch_changed W.allocator h.scratch hc ?_,
    lib_same hkeep h.library, ?_,
    cells_same (same_mono (changed_same hc) (fun a ha => h.outside_buffer (Or.inr ha))) h.cells,
    same_trans h.kept hkeep⟩
  · intro a ha hn
    unfold outsideBuffer
    by_contra hbad
    exact hn ⟨(b.toNat, 8 * W.x.m), h.scratch.buffer, by omega, by omega⟩
  · apply holds_same (changed_same hc) h.table
    intro a ha hz
    simp only [le32, List.length_map, List.length_range] at hz
    have hd := h.scratch.disjoint
    unfold outsideBuffer
    omega

theorem LoopState.column {W : World} {t b : BitVec 32} {r : Nat} {s s' : Store}
    (h : LoopState W t b r s) (hc : Changed s s' (fun a => ¬ W.l.counts W.x a))
    (hcell : Cells s' W.x W.l r W.x.m) : LoopState W t b (r + 1) s' := by
  have hkeep := same_mono (changed_same hc) W.separated
  refine ⟨linked_changed h.linked hc, scratch_changed W.allocator h.scratch hc ?_,
    lib_same hkeep h.library, ?_, cells_next hcell, same_trans h.kept hkeep⟩
  · intro a ha hn hcount
    rcases W.callerSafe a (Or.inr hcount) with hp | hp
    · exact hp ha
    · exact hn (inBlocks_mono h.scratch.old hp)
  · apply holds_same (changed_same hc) h.table
    intro a ha hz
    apply h.table_not_counts ha
    simpa [le32] using hz

theorem cells_initial {s : Store} {x : Input} {l : Layout} (h : Data s x l) :
    Cells s x l 0 0 := by
  intro u hu v hv
  exact ⟨fun hd => by simp [Done] at hd, fun _ => h.2.2.2.2.2 u hu v hv⟩

end Subjects.EdgerCpm.Body
