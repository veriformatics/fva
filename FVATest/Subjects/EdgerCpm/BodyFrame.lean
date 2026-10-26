import FVATest.Subjects.EdgerCpm.BodyMemory

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec

/-- Only memory 0 changes, with its allocation unchanged and the stated bytes preserved. -/
def Changed (s₀ s : Store) (P : Nat → Prop) : Prop :=
  ∃ before after, s₀.mems[0]? = some before ∧ s.mems[0]? = some after ∧
    s = { s₀ with mems := s₀.mems.set 0 after } ∧ after.pages = before.pages ∧
    after.max = before.max ∧ ∀ a, P a → after.byte a = before.byte a

theorem changed_refl {s : Store} {mem : MemInst} {P : Nat → Prop}
    (hm : s.mems[0]? = some mem) : Changed s s P := by
  have hset : s.mems.set 0 mem = s.mems := by
    obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.mp hm
    rw [← he]
    exact List.set_getElem_self h
  exact ⟨mem, mem, hm, hm, by rw [hset], rfl, rfl, fun _ _ => rfl⟩

theorem changed_same {s₀ s : Store} {P : Nat → Prop} (h : Changed s₀ s P) : SameOn s₀ s P := by
  obtain ⟨before, after, hb, ha, -, hp, -, he⟩ := h
  exact ⟨before, after, hb, ha, by simp [MemInst.size, hp], fun a hP _ => he a hP⟩

theorem changed_funcs {s₀ s : Store} {P : Nat → Prop} (h : Changed s₀ s P) :
    s.funcs = s₀.funcs := by
  obtain ⟨_, _, _, _, rfl, _⟩ := h
  rfl

theorem changed_size {s₀ s : Store} {P : Nat → Prop} {mem₀ mem : MemInst}
    (h : Changed s₀ s P) (hm₀ : s₀.mems[0]? = some mem₀) (hm : s.mems[0]? = some mem) :
    mem.size = mem₀.size := by
  obtain ⟨before, after, hb, ha, -, hp, -⟩ := h
  have hbefore : before = mem₀ := Option.some.inj (hb.symm.trans hm₀)
  have hafter : after = mem := Option.some.inj (ha.symm.trans hm)
  subst before after
  simp only [MemInst.size, hp]

theorem changed_put {s₀ s : Store} {P : Nat → Prop} {mem : MemInst} {p k v : Nat}
    (h : Changed s₀ s P) (hm : s.mems[0]? = some mem)
    (hP : ∀ a, P a → ¬ (p ≤ a ∧ a < p + k)) : Changed s₀ (put s mem p k v) P := by
  obtain ⟨before, after, hb, ha, hs, hp, hx, he⟩ := h
  have hafter : after = mem := Option.some.inj (ha.symm.trans hm)
  subst after
  refine ⟨before, mem.write p k v, hb, put_mem hm p k v, ?_, hp, hx, ?_⟩
  · simp only [put, hs, List.set_set]
  · intro a ha
    rw [MemInst.write_byte, ite_eq_right (hP a ha)]
    exact he a ha

theorem changed_allocator {H : HostSem} {alloc free cap k : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    {s₀ s : Store} {P : Nat → Prop} (hA : Allocator H alloc free heap cap blocks ready)
    (h : Changed s₀ s P) (hr : ready k s₀)
    (hP : ∀ a, heap a → ¬ InBlocks (blocks s₀) a → P a) :
    blocks s = blocks s₀ ∧ ready k s := by
  obtain ⟨before, after, hb, -, rfl, hp, hx, he⟩ := h
  exact hA.frame k s₀ before after hr hb hp hx (fun a ha hn => he a (hP a ha hn))

def LibData (s : Store) (x : Input) (l : Layout) : Prop :=
  Holds s l.lib (le32 (.ofNat 32 l.d)) ∧
  Holds s (l.lib + 12) (le32 (.ofNat 32 x.m) ++ le32 2) ∧
  Holds s (l.lib + 28) (le32 0) ∧
  ∀ j < x.m, Holds s (l.d + 8 * j) (le64 (x.libSize j))

theorem data_lib {s : Store} {x : Input} {l : Layout} (h : Data s x l) : LibData s x l :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem lib_same {s s' : Store} {x : Input} {l : Layout}
    (hs : SameOn s s' (l.kept x)) (h : LibData s x l) : LibData s' x l := by
  rcases h with ⟨hp, hm, hr, hd⟩
  refine ⟨holds_same hs hp ?_, holds_same hs hm ?_, holds_same hs hr ?_,
    fun j hj => holds_same hs (hd j hj) ?_⟩
  · intro a ha hb; right; left
    simp only [le32, List.length_map, List.length_range] at hb
    omega
  · intro a ha hb; right; left
    simp only [le32, List.length_append, List.length_map, List.length_range] at hb
    omega
  · intro a ha hb; right; left
    simp only [le32, List.length_map, List.length_range] at hb
    omega
  · intro a ha hb; right; right
    simp [le64, Binary.leBytes] at hb
    omega

end Subjects.EdgerCpm.Body
