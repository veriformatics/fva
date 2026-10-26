import FVATest.Subjects.EdgerCpm.BodySupport

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem same_refl {s : Store} {P : Nat → Prop} {mem : MemInst}
    (hm : s.mems[0]? = some mem) : SameOn s s P :=
  ⟨mem, mem, hm, hm, le_refl _, fun _ _ _ => rfl⟩

theorem same_mono {s s' : Store} {P Q : Nat → Prop}
    (h : SameOn s s' P) (hPQ : ∀ a, Q a → P a) : SameOn s s' Q := by
  obtain ⟨m, m', hm, hm', hb, he⟩ := h
  exact ⟨m, m', hm, hm', hb, fun a ha hn => he a (hPQ a ha) hn⟩

theorem same_trans {s s' s'' : Store} {P : Nat → Prop}
    (h : SameOn s s' P) (h' : SameOn s' s'' P) : SameOn s s'' P := by
  obtain ⟨m, m', hm, hm', hb, he⟩ := h
  obtain ⟨n, m'', hn, hm'', hb', he'⟩ := h'
  have hn' : n = m' := Option.some.inj (hn.symm.trans hm')
  subst n
  exact ⟨m, m'', hm, hm'', hb.trans hb', fun a ha hi =>
    (he' a ha (lt_of_lt_of_le hi hb)).trans (he a ha hi)⟩

theorem holds_same {s s' : Store} {P : Nat → Prop} {p : Nat} {bs : List UInt8}
    (hs : SameOn s s' P) (h : Holds s p bs)
    (hP : ∀ a, p ≤ a → a < p + bs.length → P a) : Holds s' p bs := by
  obtain ⟨m, m', hm, hm', hb, he⟩ := hs
  obtain ⟨n, hn, hnsize, hnbytes⟩ := h
  have hn' : n = m := Option.some.inj (hn.symm.trans hm)
  subst n
  refine ⟨m', hm', hnsize.trans hb, ?_⟩
  intro i hi
  exact (he (p + i) (hP _ (by omega) (by omega)) (by omega)).trans (hnbytes i hi)

theorem data_same {s s' : Store} {x : Input} {l : Layout}
    (hs : SameOn s s' fun a => l.kept x a ∨ l.counts x a) (h : Data s x l) : Data s' x l := by
  rcases h with ⟨hy, hp, hm, hr, hd, hc⟩
  refine ⟨holds_same hs hy ?_, holds_same hs hp ?_, holds_same hs hm ?_,
    holds_same hs hr ?_, fun j hj => holds_same hs (hd j hj) ?_,
    fun i hi j hj => holds_same hs (hc i hi j hj) ?_⟩
  · intro a ha hb; left; left; simpa [le32] using And.intro ha hb
  · intro a ha hb; left; right; left; simp only [le32, List.length_map,
      List.length_range] at hb; omega
  · intro a ha hb; left; right; left
    simp only [le32, List.length_append, List.length_map, List.length_range] at hb
    omega
  · intro a ha hb; left; right; left
    simp only [le32, List.length_map, List.length_range] at hb
    omega
  · intro a ha hb; left; right; right
    simp [le64, Binary.leBytes] at hb
    omega
  · intro a ha hb; right
    simp only [Layout.cell] at ha hb
    simp [le64, Binary.leBytes] at hb
    unfold Layout.counts
    have hj' : j + 1 ≤ x.m := by omega
    have hp := Nat.mul_le_mul_left x.n hj'
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hp ⊢
    omega

def put (s : Store) (mem : MemInst) (p k v : Nat) : Store :=
  { s with mems := s.mems.set 0 (mem.write p k v) }

theorem put_mem {s : Store} {mem : MemInst} (hm : s.mems[0]? = some mem) (p k v : Nat) :
    (put s mem p k v).mems[0]? = some (mem.write p k v) := by
  exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp hm).choose

theorem same_put {s : Store} {mem : MemInst} {p k v : Nat} {P : Nat → Prop}
    (hm : s.mems[0]? = some mem) (hP : ∀ a, P a → ¬ (p ≤ a ∧ a < p + k)) :
    SameOn s (put s mem p k v) P := by
  refine ⟨mem, mem.write p k v, hm, put_mem hm p k v, le_refl _, ?_⟩
  intro a ha _
  exact ite_eq_right (hP a ha)

theorem holds_put32 {s : Store} {mem : MemInst} {p : Nat} {v : BitVec 32}
    (hm : s.mems[0]? = some mem) (hb : p + 4 ≤ mem.size) :
    Holds (put s mem p 4 v.toNat) p (le32 v) := by
  refine ⟨mem.write p 4 v.toNat, put_mem hm p 4 v.toNat, by simpa [le32] using hb, ?_⟩
  intro i hi
  have hi' : i < 4 := by simpa [le32] using hi
  rw [MemInst.write_byte, ite_eq_left (by omega), show p + i - p = i by omega]
  simp [le32, List.getElem!_eq_getElem?_getD, List.getElem?_range hi']

theorem holds_put64 {s : Store} {mem : MemInst} {p : Nat} {v : BitVec 64}
    (hm : s.mems[0]? = some mem) (hb : p + 8 ≤ mem.size) :
    Holds (put s mem p 8 v.toNat) p (le64 v) := by
  refine ⟨mem.write p 8 v.toNat, put_mem hm p 8 v.toNat,
    by simpa [le64, Binary.leBytes] using hb, ?_⟩
  intro i hi
  have hi' : i < 8 := by simpa [le64, Binary.leBytes] using hi
  rw [MemInst.write_byte, ite_eq_left (by omega), show p + i - p = i by omega]
  interval_cases i <;> simp only [le64, Binary.leBytes, List.getElem!_cons_zero,
    List.getElem!_cons_succ, Nat.div_div_eq_div_mul, Nat.reduceMul, Nat.reducePow,
    Nat.pow_zero, Nat.div_one] <;> apply UInt8.toNat_inj.mp <;> simp

theorem put_frame {H : HostSem} {alloc free cap k p n v : Nat} {heap : Nat → Prop}
    {blocks : Store → List (Nat × Nat)} {ready : Nat → Store → Prop}
    (hA : Allocator H alloc free heap cap blocks ready) {s : Store} {mem : MemInst}
    (hr : ready k s) (hm : s.mems[0]? = some mem)
    (hP : ∀ a, p ≤ a → a < p + n → ¬ heap a ∨ InBlocks (blocks s) a) :
    blocks (put s mem p n v) = blocks s ∧ ready k (put s mem p n v) := by
  apply hA.frame k s mem (mem.write p n v) hr hm rfl rfl
  intro a ha hn
  rw [MemInst.write_byte, ite_eq_right]
  intro h
  exact (hP a h.1 h.2).elim (fun hh => hh ha) hn

theorem linked_extends {s s' : Store} {inst : ModuleInst} {alloc free : Nat}
    (h : Linked s inst alloc free) (he : Store.Extends s s') : Linked s' inst alloc free := by
  obtain ⟨hm, a160, a207, a12, a13, h207, h12, h13, hex, f160, f207, f12, f13⟩ := h
  have keep : ∀ (a : Nat) (f : FuncInst), s.funcs[a]? = some f → s'.funcs[a]? = some f := by
    intro a f hf
    obtain ⟨g, hg, rfl⟩ := he.1 a f hf
    exact hg
  exact ⟨hm, a160, a207, a12, a13, h207, h12, h13, hex,
    keep _ _ f160, keep _ _ f207, keep _ _ f12, keep _ _ f13⟩

theorem linked_put {s : Store} {inst : ModuleInst} {alloc free p k v : Nat} {mem : MemInst}
    (h : Linked s inst alloc free) : Linked (put s mem p k v) inst alloc free := h

end Subjects.EdgerCpm.Body
