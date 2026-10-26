import FVATest.Subjects.EdgerCpm.BodyCopy

namespace Subjects.EdgerCpm.Body

open FVA.Wasm FVA.Wasm.Exec

def Done (r j u v : Nat) : Prop := u < r ∨ u = r ∧ v < j

def Cells (s : Store) (x : Input) (l : Layout) (r j : Nat) : Prop :=
  ∀ u < x.n, ∀ v < x.m,
    (Done r j u v → ∃ out, Holds s (l.cell x u v) (le64 out) ∧
      CpmElem (x.count u v) (x.libSize v) out) ∧
    (¬ Done r j u v → Holds s (l.cell x u v) (le64 (x.count u v)))

theorem cell_end {x : Input} {l : Layout} {u v : Nat} (hu : u < x.n) (hv : v < x.m) :
    l.cell x u v + 8 ≤ l.c + 8 * x.n * x.m := by
  have hmul := Nat.mul_le_mul_left x.n (by omega : v + 1 ≤ x.m)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  simp only [Layout.cell, Nat.mul_assoc]
  omega

theorem cell_counts {x : Input} {l : Layout} {u v a : Nat}
    (hu : u < x.n) (hv : v < x.m) (ha : l.cell x u v ≤ a) (hb : a < l.cell x u v + 8) :
    l.counts x a := by
  have he := cell_end (l := l) hu hv
  unfold Layout.counts
  have hs : l.c ≤ l.cell x u v := Nat.le_add_right _ _
  omega

theorem cells_disjoint {x : Input} {l : Layout} {r j u v : Nat}
    (hr : r < x.n) (hu : u < x.n) (hne : u ≠ r ∨ v ≠ j) :
    l.cell x u v + 8 ≤ l.cell x r j ∨ l.cell x r j + 8 ≤ l.cell x u v := by
  by_cases hvj : v = j
  · subst v
    have hur : u ≠ r := by simpa using hne
    simp only [Layout.cell]
    omega
  · rcases lt_or_gt_of_ne hvj with h | h
    · left
      have hmul := Nat.mul_le_mul_left x.n (by omega : v + 1 ≤ j)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      simp only [Layout.cell]
      omega
    · right
      have hmul := Nat.mul_le_mul_left x.n (by omega : j + 1 ≤ v)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      simp only [Layout.cell]
      omega

theorem cells_put {s : Store} {mem : MemInst} {x : Input} {l : Layout} {r j : Nat}
    {out : BitVec 64} (hr : r < x.n) (hj : j < x.m) (hm : s.mems[0]? = some mem)
    (hb : l.cell x r j + 8 ≤ mem.size) (hc : Cells s x l r j)
    (hout : CpmElem (x.count r j) (x.libSize j) out) :
    Cells (put s mem (l.cell x r j) 8 out.toNat) x l r (j + 1) := by
  intro u hu v hv
  by_cases htarget : u = r ∧ v = j
  · obtain ⟨rfl, rfl⟩ := htarget
    exact ⟨fun _ => ⟨out, holds_put64 hm hb, hout⟩,
      fun hn => False.elim (hn (Or.inr ⟨rfl, by omega⟩))⟩
  · have hneq : u ≠ r ∨ v ≠ j := by omega
    have hdis := cells_disjoint (l := l) hr hu hneq
    have same := same_put hm (p := l.cell x r j) (k := 8) (v := out.toNat)
      (P := fun a => l.cell x u v ≤ a ∧ a < l.cell x u v + 8)
      (by intro a ha hz; omega)
    have hp : ∀ {bs : List UInt8}, bs.length = 8 → Holds s (l.cell x u v) bs →
        Holds (put s mem (l.cell x r j) 8 out.toNat) (l.cell x u v) bs := by
      intro bs hlen hholds
      apply holds_same same hholds
      intro a ha hz
      simpa only [hlen] using And.intro ha hz
    have hd : Done r (j + 1) u v ↔ Done r j u v := by unfold Done; omega
    refine ⟨?_, fun hn => hp (by simp [le64, Binary.leBytes])
      ((hc u hu v hv).2 (fun h => hn (hd.mpr h)))⟩
    intro h
    obtain ⟨o, ho, he⟩ := (hc u hu v hv).1 (hd.mp h)
    exact ⟨o, hp (by simp [le64, Binary.leBytes]) ho, he⟩

theorem cells_next {s : Store} {x : Input} {l : Layout} {r : Nat}
    (h : Cells s x l r x.m) : Cells s x l (r + 1) 0 := by
  intro u hu v hv
  have hd : Done (r + 1) 0 u v ↔ Done r x.m u v := by unfold Done; omega
  exact ⟨fun hg => (h u hu v hv).1 (hd.mp hg),
    fun hn => (h u hu v hv).2 (fun hg => hn (hd.mpr hg))⟩

theorem cells_same {s s' : Store} {x : Input} {l : Layout} {r j : Nat}
    (hs : SameOn s s' (l.counts x)) (h : Cells s x l r j) : Cells s' x l r j := by
  intro u hu v hv
  have keep : ∀ {bs : List UInt8}, bs.length = 8 → Holds s (l.cell x u v) bs →
      Holds s' (l.cell x u v) bs := by
    intro bs hlen hh
    apply holds_same hs hh
    intro a ha hb
    apply cell_counts hu hv ha
    simpa only [hlen] using hb
  refine ⟨?_, fun hn => keep (by simp [le64, Binary.leBytes]) ((h u hu v hv).2 hn)⟩
  intro hd
  obtain ⟨o, ho, he⟩ := (h u hu v hv).1 hd
  exact ⟨o, keep (by simp [le64, Binary.leBytes]) ho, he⟩

end Subjects.EdgerCpm.Body
