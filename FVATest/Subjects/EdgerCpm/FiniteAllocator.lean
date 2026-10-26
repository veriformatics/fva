import FVATest.Subjects.EdgerCpm.ExistenceMem

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec

set_option maxHeartbeats 0

namespace FiniteAllocator

def capacity : Nat := 2 ^ 29
def base : Nat := 2 ^ 30 + 2 ^ 20
def slot₀ : Nat := base + 8
def slot₁ : Nat := slot₀ + capacity
def limit : Nat := slot₁ + capacity
def heap (a : Nat) : Prop := base ≤ a ∧ a < limit

def size₀ (m : MemInst) : Nat := m.read base 4
def size₁ (m : MemInst) : Nat := m.read (base + 4) 4

def entries (u v : Nat) : List (Nat × Nat) :=
  (if u = 0 then [] else [(slot₀, u)]) ++ (if v = 0 then [] else [(slot₁, v)])

def blocks (s : Store) : List (Nat × Nat) :=
  match s.mems[0]? with
  | some m => entries (size₀ m) (size₁ m)
  | none => []

-- Two allocations suffice; free need not reclaim storage for this contract.
def Budget (cap k u v : Nat) : Prop :=
  (u = 0 ∧ v = 0 ∧ k ≤ 2) ∨
  (0 < u ∧ u ≤ cap ∧ v = 0 ∧ k ≤ 1) ∨
  (0 < u ∧ u ≤ cap ∧ 0 < v ∧ v ≤ cap ∧ k = 0)

def ready (cap k : Nat) (s : Store) : Prop :=
  ∃ m, s.mems[0]? = some m ∧ limit ≤ m.size ∧ Budget cap k (size₀ m) (size₁ m)

def first (m : MemInst) (z : Nat) : MemInst :=
  (m.write base 4 z).fill slot₀ z (fun _ => 0)

def second (m : MemInst) (z : Nat) : MemInst :=
  (m.write (base + 4) 4 z).fill slot₁ z (fun _ => 0)

def allocate (m : MemInst) (z : Nat) : MemInst × Nat :=
  if size₀ m = 0 then (first m z, slot₀) else (second m z, slot₁)

def host : HostSem
  | 12, s, [.i32 n, .i32 sz], o => ∃ m, s.mems[0]? = some m ∧
      o = .returned { s with mems := s.mems.set 0 (allocate m (n.toNat * sz.toNat)).1 }
        [.i32 (.ofNat 32 (allocate m (n.toNat * sz.toNat)).2)]
  | 13, s, [.i32 _], o => o = .returned s []
  | _, _, _, _ => False

theorem inEntries {u v a : Nat} : InBlocks (entries u v) a ↔
    (u ≠ 0 ∧ slot₀ ≤ a ∧ a < slot₀ + u) ∨
      (v ≠ 0 ∧ slot₁ ≤ a ∧ a < slot₁ + v) := by
  by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [entries, hu, hv, InBlocks]

theorem blocks_above {s : Store} {a : Nat} (h : InBlocks (blocks s) a) : slot₀ ≤ a := by
  unfold blocks at h
  split at h
  · rcases inEntries.mp h with h | h
    · exact h.2.1
    · exact Nat.le_trans (by unfold slot₁; omega) h.2.1
  · simp [InBlocks] at h

theorem budget_next {cap k u v : Nat} (h : Budget cap (k + 1) u v) :
    v = 0 ∧ ((u = 0 ∧ k ≤ 1) ∨ (0 < u ∧ u ≤ cap ∧ k = 0)) := by
  unfold Budget at h
  omega

theorem first_sizes (m : MemInst) {z : Nat} (hz : z ≤ capacity) :
    size₀ (first m z) = z ∧ size₁ (first m z) = size₁ m := by
  have hz' : z < 256 ^ 4 := by unfold capacity at hz; omega
  constructor
  · unfold size₀ first
    rw [read_fill_disjoint _ _ (Or.inl (by unfold slot₀; omega)),
      MemInst.read_write_self, Nat.mod_eq_of_lt hz']
  · unfold size₁ first
    rw [read_fill_disjoint _ _ (Or.inl (by unfold slot₀; omega)),
      MemInst.read_write_of_disjoint _ (Or.inr (by omega))]

theorem second_sizes (m : MemInst) {z : Nat} (hz : z ≤ capacity) :
    size₀ (second m z) = size₀ m ∧ size₁ (second m z) = z := by
  have hz' : z < 256 ^ 4 := by unfold capacity at hz; omega
  constructor
  · unfold size₀ second
    rw [read_fill_disjoint _ _ (Or.inl (by unfold slot₁ slot₀; omega)),
      MemInst.read_write_of_disjoint _ (Or.inl (by omega))]
  · unfold size₁ second
    rw [read_fill_disjoint _ _ (Or.inl (by unfold slot₁ slot₀; omega)),
      MemInst.read_write_self, Nat.mod_eq_of_lt hz']

theorem frame (cap k : Nat) {s : Store} {m m' : MemInst} (hr : ready cap k s)
    (hm : s.mems[0]? = some m) (hp : m'.pages = m.pages) (_hx : m'.max = m.max)
    (hb : ∀ a, heap a → ¬ InBlocks (blocks s) a → m'.byte a = m.byte a) :
    blocks { s with mems := s.mems.set 0 m' } = blocks s ∧
      ready cap k { s with mems := s.mems.set 0 m' } := by
  have hmeta : ∀ a, base ≤ a → a < base + 8 → m'.byte a = m.byte a := by
    intro a ha ha'
    apply hb a
    · constructor
      · exact ha
      · unfold limit slot₁ slot₀; omega
    · intro hi
      have hi' := blocks_above hi
      unfold slot₀ at hi'
      omega
  have h₀ : size₀ m' = size₀ m := read_congr fun a h₁ h₂ => hmeta a h₁ (by omega)
  have h₁ : size₁ m' = size₁ m := read_congr fun a h₁ h₂ => hmeta a (by omega) (by omega)
  have hm' := setMem_zero hm m'
  constructor
  · simp only [blocks, hm', hm, h₀, h₁]
  · rcases hr with ⟨m₀, hm₀, hfit, hbudget⟩
    have heq : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
    subst m₀
    refine ⟨m', hm', ?_, ?_⟩
    · simpa only [MemInst.size, hp] using hfit
    · simpa only [h₀, h₁] using hbudget

def Allocated (cap k : Nat) (s : Store) (m' : MemInst) (p z : Nat) : Prop :=
  let s' := { s with mems := s.mems.set 0 m' }
  Store.Extends s s' ∧ ready cap k s' ∧ p + z ≤ 2 ^ 32 ∧
    (∀ a, p ≤ a → a < p + z → heap a ∧ ¬ InBlocks (blocks s) a) ∧
    Holds s' p (List.replicate z 0) ∧
    (p, z) ∈ blocks s' ∧ (∀ b ∈ blocks s, b ∈ blocks s') ∧
    SameOn s s' fun a => ¬ heap a ∨ InBlocks (blocks s) a

theorem filled_zero {s : Store} {m : MemInst} {q p z : Nat}
    (hm : s.mems[0]? = some m) (hfit : p + z ≤ m.size) :
    Holds { s with mems := s.mems.set 0 ((m.write q 4 z).fill p z (fun _ => 0)) }
      p (List.replicate z 0) := by
  refine ⟨_, setMem_zero hm _, ?_, ?_⟩
  · change p + (List.replicate z (0 : UInt8)).length ≤ m.size
    simpa only [List.length_replicate] using hfit
  · intro i hi
    simp only [List.length_replicate] at hi
    have hr : p ≤ p + i ∧ p + i < p + z := by omega
    simp [MemInst.fill, hr, hi]

theorem changed_bytes {m : MemInst} {q p z a : Nat}
    (hq : ¬ (q ≤ a ∧ a < q + 4)) (hp : ¬ (p ≤ a ∧ a < p + z)) :
    ((m.write q 4 z).fill p z (fun _ => 0)).byte a = m.byte a := by
  simp only [MemInst.fill, hp, ite_false, MemInst.write_byte, hq]

theorem first_allocated {cap k : Nat} {s : Store} {m : MemInst} {z : Nat}
    (hc : cap ≤ capacity) (hm : s.mems[0]? = some m) (hfit : limit ≤ m.size)
    (h₀ : size₀ m = 0) (h₁ : size₁ m = 0) (hk : k ≤ 1)
    (hz : 0 < z) (hzc : z ≤ cap) : Allocated cap k s (first m z) slot₀ z := by
  have hzs : z ≤ capacity := hzc.trans hc
  have hsizes := first_sizes m hzs
  have hp : slot₀ + z ≤ limit := by unfold limit slot₁; omega
  have hpbase : base ≤ slot₀ := by unfold slot₀; omega
  have hmeta : base + 4 ≤ slot₀ := by unfold slot₀; omega
  have hm' := setMem_zero hm (first m z)
  have hbs : blocks s = [] := by simp [blocks, hm, h₀, h₁, entries]
  have hbs' : blocks { s with mems := s.mems.set 0 (first m z) } = [(slot₀, z)] := by
    simp [blocks, hm', hsizes.1, hsizes.2, h₁, entries, Nat.ne_of_gt hz]
  refine ⟨setMem_extends hm rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨first m z, hm', hfit, ?_⟩
    rw [hsizes.1, hsizes.2, h₁]
    exact Or.inr (Or.inl ⟨hz, hzc, rfl, hk⟩)
  · exact hp.trans (by decide)
  · intro a ha ha'
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp [hbs, InBlocks]
  · exact filled_zero hm (hp.trans hfit)
  · simp [hbs']
  · simp [hbs]
  · apply sameOn_setMem (m' := first m z) hm (Nat.le_refl _)
    intro a hkeep _
    have hout : ¬ heap a := by simpa [hbs, InBlocks] using hkeep
    apply changed_bytes
    · intro ha
      exact hout ⟨ha.1, by omega⟩
    · intro ha
      exact hout ⟨by omega, by omega⟩

theorem second_allocated {cap : Nat} {s : Store} {m : MemInst} {z : Nat}
    (hc : cap ≤ capacity) (hm : s.mems[0]? = some m) (hfit : limit ≤ m.size)
    (h₀ : 0 < size₀ m) (h₀c : size₀ m ≤ cap) (h₁ : size₁ m = 0)
    (hz : 0 < z) (hzc : z ≤ cap) : Allocated cap 0 s (second m z) slot₁ z := by
  have hzs : z ≤ capacity := hzc.trans hc
  have hus : size₀ m ≤ capacity := h₀c.trans hc
  have hsizes := second_sizes m hzs
  have hp : slot₁ + z ≤ limit := by unfold limit; omega
  have hpbase : base ≤ slot₁ := by unfold slot₁ slot₀; omega
  have hmeta : base + 8 ≤ slot₀ := by unfold slot₀; omega
  have hsep : slot₀ + size₀ m ≤ slot₁ := by unfold slot₁; omega
  have hm' := setMem_zero hm (second m z)
  have hbs : blocks s = [(slot₀, size₀ m)] := by
    simp [blocks, hm, h₁, entries, Nat.ne_of_gt h₀]
  have hbs' : blocks { s with mems := s.mems.set 0 (second m z) } =
      [(slot₀, size₀ m), (slot₁, z)] := by
    simp [blocks, hm', hsizes.1, hsizes.2, entries, Nat.ne_of_gt h₀, Nat.ne_of_gt hz]
  refine ⟨setMem_extends hm rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨second m z, hm', hfit, ?_⟩
    rw [hsizes.1, hsizes.2]
    exact Or.inr (Or.inr ⟨h₀, h₀c, hz, hzc, rfl⟩)
  · exact hp.trans (by decide)
  · intro a ha ha'
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [hbs, InBlocks, List.mem_singleton, exists_eq_left]
    omega
  · exact filled_zero hm (hp.trans hfit)
  · simp [hbs']
  · intro b hb
    simp only [hbs, List.mem_singleton] at hb
    simp [hbs', hb]
  · apply sameOn_setMem (m' := second m z) hm (Nat.le_refl _)
    intro a hkeep _
    rcases hkeep with hout | hin
    · apply changed_bytes
      · intro ha
        exact hout ⟨by omega, by omega⟩
      · intro ha
        exact hout ⟨by omega, by omega⟩
    · simp only [hbs, InBlocks, List.mem_singleton, exists_eq_left] at hin
      apply changed_bytes <;> omega

theorem allocate_spec {cap k : Nat} {s : Store} {m : MemInst} {z : Nat}
    (hc : cap ≤ capacity) (hr : ready cap (k + 1) s) (hm : s.mems[0]? = some m)
    (hz : 0 < z) (hzc : z ≤ cap) :
    Allocated cap k s (allocate m z).1 (allocate m z).2 z := by
  rcases hr with ⟨m₀, hm₀, hfit, hbudget⟩
  have heq : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
  subst m₀
  rcases budget_next hbudget with ⟨h₁, (⟨h₀, hk⟩ | ⟨h₀, h₀c, rfl⟩)⟩
  · simpa only [allocate, h₀, ite_true] using first_allocated hc hm hfit h₀ h₁ hk hz hzc
  · simpa only [allocate, Nat.ne_of_gt h₀, ite_false] using
      second_allocated hc hm hfit h₀ h₀c h₁ hz hzc

theorem allocate_ptr (m : MemInst) (z : Nat) : (allocate m z).2 < 2 ^ 32 := by
  unfold allocate
  split
  · change slot₀ < 2 ^ 32
    decide
  · change slot₁ < 2 ^ 32
    decide

theorem allocator (cap : Nat) (hc : cap ≤ capacity) :
    Allocator host 12 13 heap cap blocks (ready cap) := by
  constructor
  · intro k s n sz hr hz hzc
    rcases hr with ⟨m, hm, hfit, hbudget⟩
    have hr : ready cap (k + 1) s := ⟨m, hm, hfit, hbudget⟩
    constructor
    · exact ⟨_, m, hm, rfl⟩
    · intro o ho
      rcases ho with ⟨m₀, hm₀, heq⟩
      have hmem : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
      subst m₀
      refine ⟨_, .ofNat 32 (allocate m (n.toNat * sz.toNat)).2, heq, ?_⟩
      simpa only [Allocated, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (allocate_ptr m _)] using
        allocate_spec hc hr hm hz hzc
  · intro k s p _ hr _
    constructor
    · exact ⟨_, rfl⟩
    · intro o ho
      refine ⟨s, ho, Store.Extends.refl s, hr, fun _ hb _ => hb, ?_⟩
      rcases hr with ⟨m, hm, _, _⟩
      exact ⟨m, m, hm, hm, Nat.le_refl _, fun _ _ _ => rfl⟩
  · intro k s m m' hr hm hp hx hb
    exact frame cap k hr hm hp hx hb

end FiniteAllocator

end Subjects.EdgerCpm.Existence
