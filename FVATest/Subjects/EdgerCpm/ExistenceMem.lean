import FVATest.Subjects.EdgerCpm.Spec
import FVATest.Subjects.EdgerCpm.MemWrite
import FVA.Proof.Valid.Updates

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec

set_option maxHeartbeats 0

theorem read_congr {m m' : MemInst} {p n : Nat}
    (h : ∀ a, p ≤ a → a < p + n → m'.byte a = m.byte a) :
    m'.read p n = m.read p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [MemInst.read, h p (by omega) (by omega)]
    rw [ih (fun a h₁ h₂ => h a (by omega) (by omega))]

theorem read_fill_disjoint (m : MemInst) {p n q k : Nat} (f : Nat → UInt8)
    (h : q + k ≤ p ∨ p + n ≤ q) : (m.fill p n f).read q k = m.read q k :=
  read_congr fun a h₁ h₂ => by
    have hn : ¬ (p ≤ a ∧ a < p + n) := by omega
    simp only [MemInst.fill, ite_eq_right hn]

theorem setMem_zero {s : Store} {m : MemInst} (h : s.mems[0]? = some m) (m' : MemInst) :
    (s.mems.set 0 m')[0]? = some m' :=
  List.getElem?_set_self (List.getElem?_eq_some_iff.mp h).1

theorem setMem_extends {s : Store} {m m' : MemInst} (h : s.mems[0]? = some m)
    (hp : m'.pages = m.pages) (hm : m'.max = m.max) :
    Store.Extends s { s with mems := s.mems.set 0 m' } := by
  have hr := Store.Extends.refl s
  exact ⟨hr.1, hr.2.1,
    FVA.Wasm.Valid.listExtends_set (fun _ => ⟨rfl, Nat.le_refl _⟩) h
      ⟨hm, by rw [hp]⟩,
    hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩

theorem sameOn_setMem {s : Store} {m m' : MemInst} {keep : Nat → Prop}
    (h : s.mems[0]? = some m) (hp : m.size ≤ m'.size)
    (hb : ∀ a, keep a → a < m.size → m'.byte a = m.byte a) :
    SameOn s { s with mems := s.mems.set 0 m' } keep :=
  ⟨m, m', h, setMem_zero h m', hp, hb⟩

theorem holds_fill {s : Store} {m : MemInst} {p n q : Nat} {f : Nat → UInt8}
    {bs : List UInt8} (hm : s.mems[0]? = some m) (hfit : q + bs.length ≤ m.size)
    (hlo : p ≤ q) (hhi : q + bs.length ≤ p + n)
    (hbytes : ∀ i, i < bs.length → f (q + i - p) = bs[i]!) :
    Holds { s with mems := s.mems.set 0 (m.fill p n f) } q bs := by
  refine ⟨m.fill p n f, setMem_zero hm _, hfit, ?_⟩
  intro i hi
  have hr : p ≤ q + i ∧ q + i < p + n := by omega
  simpa only [MemInst.fill, ite_eq_left hr] using hbytes i hi

theorem prep_fill {s : Store} {m : MemInst} {p n : Nat} {f : Nat → UInt8}
    (hm : s.mems[0]? = some m) (hfit : p + n ≤ m.size) :
    s.prep [.fill p n f] = some { s with mems := s.mems.set 0 (m.fill p n f) } := by
  simp only [Store.prep, hm, ite_eq_left hfit]

end Subjects.EdgerCpm.Existence
