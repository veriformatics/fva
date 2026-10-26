import FVATest.Subjects.EdgerCpm.BodyMemory

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

theorem inBlocks_mono {bs bs' : List (Nat × Nat)} {a : Nat}
    (h : ∀ b ∈ bs, b ∈ bs') (ha : InBlocks bs a) : InBlocks bs' a := by
  obtain ⟨b, hb, hi⟩ := ha
  exact ⟨b, h b hb, hi⟩

structure Scratch (heap : Nat → Prop) (blocks : Store → List (Nat × Nat))
    (ready : Nat → Store → Prop)
    (initial : List (Nat × Nat)) (m : Nat) (t b : BitVec 32) (s : Store) : Prop where
  next : ready 0 s
  old : ∀ p ∈ initial, p ∈ blocks s
  table : (t.toNat, 4) ∈ blocks s
  buffer : (b.toNat, 8 * m) ∈ blocks s
  tableBound : t.toNat + 4 ≤ 2 ^ 32
  bufferBound : b.toNat + 8 * m ≤ 2 ^ 32
  tablePrivate : ∀ a, t.toNat ≤ a → a < t.toNat + 4 → heap a ∧ ¬ InBlocks initial a
  bufferPrivate : ∀ a, b.toNat ≤ a → a < b.toNat + 8 * m → heap a ∧ ¬ InBlocks initial a
  disjoint : t.toNat + 4 ≤ b.toNat ∨ b.toNat + 8 * m ≤ t.toNat
  room : ∃ mem, s.mems[0]? = some mem ∧
    t.toNat + 4 ≤ mem.size ∧ b.toNat + 8 * m ≤ mem.size

theorem scratch_allocated {heap : Nat → Prop} {blocks : Store → List (Nat × Nat)}
    {ready : Nat → Store → Prop} {s₀ s₁ s₂ : Store} {t b : BitVec 32} {m : Nat}
    (hm : 0 < m) (ht : Allocated heap blocks ready 1 4 s₀ s₁ t)
    (hb : Allocated heap blocks ready 0 (8 * m) s₁ s₂ b) :
    Scratch heap blocks ready (blocks s₀) m t b s₂ := by
  have hT : Holds s₂ t.toNat (List.replicate 4 0) :=
    holds_same hb.same ht.zero (by
      intro a ha hz
      right
      exact ⟨(t.toNat, 4), ht.member, ha, by simpa using hz⟩)
  obtain ⟨mem, hmem, hsize, -⟩ := hb.zero
  obtain ⟨mem', hmem', hsize', -⟩ := hT
  have he : mem' = mem := Option.some.inj (hmem'.symm.trans hmem)
  subst mem'
  refine ⟨hb.next, fun p hp => hb.old p (ht.old p hp), hb.old _ ht.member, hb.member,
    ht.bound, hb.bound, ht.fresh, ?_, ?_,
    mem, hmem, by simpa using hsize', by simpa using hsize⟩
  · intro a ha hz
    obtain ⟨hheap, hnot⟩ := hb.fresh a ha hz
    exact ⟨hheap, fun h => hnot (inBlocks_mono ht.old h)⟩
  · by_contra h
    have h1 : t.toNat < b.toNat + 8 * m := by omega
    have h2 : b.toNat < t.toNat + 4 := by omega
    have h3 := (hb.fresh (max t.toNat b.toNat) (by omega) (by omega)).2
    apply h3
    exact ⟨(t.toNat, 4), ht.member, by simp, by omega⟩

theorem scratch_put {H : HostSem} {alloc free cap p k v : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    {initial : List (Nat × Nat)} {m : Nat} {t b : BitVec 32} {s : Store} {mem : MemInst}
    (hA : Allocator H alloc free heap cap blocks ready)
    (h : Scratch heap blocks ready initial m t b s) (hm : s.mems[0]? = some mem)
    (hp : ∀ a, p ≤ a → a < p + k → ¬ heap a ∨ InBlocks (blocks s) a) :
    Scratch heap blocks ready initial m t b (put s mem p k v) := by
  obtain ⟨hblocks, hr⟩ := put_frame hA h.next hm hp
  obtain ⟨mem', hmem', hts, hbs⟩ := h.room
  have he : mem' = mem := Option.some.inj (hmem'.symm.trans hm)
  subst mem'
  exact ⟨hr, by simpa only [hblocks] using h.old, by simpa only [hblocks] using h.table,
    by simpa only [hblocks] using h.buffer, h.tableBound, h.bufferBound, h.tablePrivate,
    h.bufferPrivate, h.disjoint, mem.write p k v, put_mem hm p k v, hts, hbs⟩

end Subjects.EdgerCpm.Body
