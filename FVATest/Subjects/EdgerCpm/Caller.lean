import FVATest.Subjects.EdgerCpm.FiniteAllocator

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def layout (x : Input) : Layout := ⟨65536, 65600, 65664, 65664 + 8 * x.m⟩
def span (x : Input) : Nat := 128 + 8 * x.m + 8 * x.n * x.m

def callerByte (x : Input) (a : Nat) : UInt8 :=
  if 65544 ≤ a ∧ a < 65552 then
    (le32 (.ofNat 32 x.n) ++ le32 (.ofNat 32 x.m))[a - 65544]!
  else if 65600 ≤ a ∧ a < 65604 then
    (le32 (.ofNat 32 65664))[a - 65600]!
  else if 65612 ≤ a ∧ a < 65620 then
    (le32 (.ofNat 32 x.m) ++ le32 2)[a - 65612]!
  else if 65628 ≤ a ∧ a < 65632 then (le32 0)[a - 65628]!
  else if 65664 ≤ a ∧ a < 65664 + 8 * x.m then
    (le64 (x.libSize ((a - 65664) / 8)))[(a - 65664) % 8]!
  else if 65664 + 8 * x.m ≤ a ∧ a < 65536 + span x then
    let cell := (a - (65664 + 8 * x.m)) / 8
    (le64 (x.count (cell % x.n) (cell / x.n)))[(a - (65664 + 8 * x.m)) % 8]!
  else 0

def prep (x : Input) : List Prep :=
  [.fill FiniteAllocator.base 8 (fun _ => 0),
    .fill 65536 (span x) (fun a => callerByte x (65536 + a))]

def metadataMem (m : MemInst) : MemInst := m.fill FiniteAllocator.base 8 (fun _ => 0)

def callerMem (m : MemInst) (x : Input) : MemInst :=
  (metadataMem m).fill 65536 (span x) (fun a => callerByte x (65536 + a))

def callerStore (s : Store) (m : MemInst) (x : Input) : Store :=
  { s with mems := (s.mems.set 0 (metadataMem m)).set 0 (callerMem m x) }

theorem domain_cap {x : Input} (h : Domain x) : 8 * x.m ≤ FiniteAllocator.capacity := by
  have hn : 1 ≤ x.n := h.1
  have hmn : x.m ≤ x.n * x.m := by
    simpa only [one_mul] using Nat.mul_le_mul_right x.m hn
  have hm : 8 * x.m ≤ 8 * x.n * x.m := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8 hmn
  unfold Domain at h
  unfold FiniteAllocator.capacity
  omega

theorem span_below_heap {x : Input} (h : Domain x) :
    65536 + span x ≤ FiniteAllocator.base := by
  unfold Domain at h
  unfold span FiniteAllocator.base
  omega

theorem caller_mem {s : Store} {m : MemInst} (hm : s.mems[0]? = some m) (x : Input) :
    (callerStore s m x).mems[0]? = some (callerMem m x) :=
  setMem_zero (s := { s with mems := s.mems.set 0 (metadataMem m) })
    (setMem_zero hm _) _

theorem caller_prep {x : Input} {s : Store} {m : MemInst} (hx : Domain x)
    (hm : s.mems[0]? = some m) (hfit : FiniteAllocator.limit ≤ m.size) :
    s.prep (prep x) = some (callerStore s m x) := by
  have hb : FiniteAllocator.base + 8 ≤ m.size := by
    unfold FiniteAllocator.limit FiniteAllocator.slot₁ FiniteAllocator.slot₀ at hfit
    omega
  have hc : 65536 + span x ≤ m.size :=
    (span_below_heap hx).trans (by omega)
  simp only [prep, Store.prep, hm, ite_eq_left hb]
  exact prep_fill (s := { s with mems := s.mems.set 0 (metadataMem m) })
    (setMem_zero hm _) hc

theorem caller_dims (x : Input) {i : Nat} (hi : i < 8) :
    callerByte x (65544 + i) =
      (le32 (.ofNat 32 x.n) ++ le32 (.ofNat 32 x.m))[i]! := by
  simp only [callerByte, ite_eq_left (show 65544 ≤ 65544 + i ∧ 65544 + i < 65552 by omega)]
  rw [Nat.add_sub_cancel_left]

theorem caller_ptr (x : Input) {i : Nat} (hi : i < 4) :
    callerByte x (65600 + i) = (le32 (.ofNat 32 65664))[i]! := by
  simp only [callerByte,
    ite_eq_right (show ¬ (65544 ≤ 65600 + i ∧ 65600 + i < 65552) by omega),
    ite_eq_left (show 65600 ≤ 65600 + i ∧ 65600 + i < 65604 by omega)]
  rw [Nat.add_sub_cancel_left]

theorem caller_tag (x : Input) {i : Nat} (hi : i < 8) :
    callerByte x (65612 + i) = (le32 (.ofNat 32 x.m) ++ le32 2)[i]! := by
  simp only [callerByte,
    ite_eq_right (show ¬ (65544 ≤ 65612 + i ∧ 65612 + i < 65552) by omega),
    ite_eq_right (show ¬ (65600 ≤ 65612 + i ∧ 65612 + i < 65604) by omega),
    ite_eq_left (show 65612 ≤ 65612 + i ∧ 65612 + i < 65620 by omega)]
  rw [Nat.add_sub_cancel_left]

theorem caller_rowsel (x : Input) {i : Nat} (hi : i < 4) :
    callerByte x (65628 + i) = (le32 0)[i]! := by
  simp only [callerByte,
    ite_eq_right (show ¬ (65544 ≤ 65628 + i ∧ 65628 + i < 65552) by omega),
    ite_eq_right (show ¬ (65600 ≤ 65628 + i ∧ 65628 + i < 65604) by omega),
    ite_eq_right (show ¬ (65612 ≤ 65628 + i ∧ 65628 + i < 65620) by omega),
    ite_eq_left (show 65628 ≤ 65628 + i ∧ 65628 + i < 65632 by omega)]
  rw [Nat.add_sub_cancel_left]

theorem caller_lib {x : Input} {j i : Nat} (hj : j < x.m) (hi : i < 8) :
    callerByte x (65664 + 8 * j + i) = (le64 (x.libSize j))[i]! := by
  have haddr : 65664 ≤ 65664 + 8 * j + i ∧
      65664 + 8 * j + i < 65664 + 8 * x.m := by omega
  simp only [callerByte,
    ite_eq_right (show ¬ (65544 ≤ 65664 + 8 * j + i ∧ 65664 + 8 * j + i < 65552) by omega),
    ite_eq_right (show ¬ (65600 ≤ 65664 + 8 * j + i ∧ 65664 + 8 * j + i < 65604) by omega),
    ite_eq_right (show ¬ (65612 ≤ 65664 + 8 * j + i ∧ 65664 + 8 * j + i < 65620) by omega),
    ite_eq_right (show ¬ (65628 ≤ 65664 + 8 * j + i ∧ 65664 + 8 * j + i < 65632) by omega),
    ite_eq_left haddr]
  have hdiv : (65664 + 8 * j + i - 65664) / 8 = j := by omega
  have hmod : (65664 + 8 * j + i - 65664) % 8 = i := by omega
  rw [hdiv, hmod]

theorem cell_bound {x : Input} {i j : Nat} (hi : i < x.n) (hj : j < x.m) :
    i + x.n * j + 1 ≤ x.n * x.m := by
  have hmul := Nat.mul_le_mul_left x.n (show j + 1 ≤ x.m by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

theorem caller_count {x : Input} {i j k : Nat} (hi : i < x.n) (hj : j < x.m)
    (hk : k < 8) : callerByte x ((layout x).cell x i j + k) = (le64 (x.count i j))[k]! := by
  have hb := cell_bound hi hj
  have hd : ((layout x).cell x i j + k - (65664 + 8 * x.m)) / 8 = i + x.n * j := by
    dsimp only [Layout.cell, layout]
    omega
  have hm : ((layout x).cell x i j + k - (65664 + 8 * x.m)) % 8 = k := by
    dsimp only [Layout.cell, layout]
    omega
  have hmod : (i + x.n * j) % x.n = i := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hdiv : (i + x.n * j) / x.n = j := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hspan : (layout x).cell x i j + k < 65536 + span x := by
    dsimp only [Layout.cell, layout, span]
    have hscaled := Nat.mul_le_mul_left 8 hb
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hscaled ⊢
    omega
  have hlo : 65664 + 8 * x.m ≤ (layout x).cell x i j + k := by
    dsimp only [Layout.cell, layout]
    omega
  have hcount : 65664 + 8 * x.m ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65536 + span x := ⟨hlo, hspan⟩
  simp only [callerByte,
    ite_eq_right (show ¬ (65544 ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65552) by omega),
    ite_eq_right (show ¬ (65600 ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65604) by omega),
    ite_eq_right (show ¬ (65612 ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65620) by omega),
    ite_eq_right (show ¬ (65628 ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65632) by omega),
    ite_eq_right (show ¬ (65664 ≤ (layout x).cell x i j + k ∧
      (layout x).cell x i j + k < 65664 + 8 * x.m) by omega),
    ite_eq_left hcount, hd, hm, hmod, hdiv]

theorem caller_holds {x : Input} {s : Store} {m : MemInst} {q : Nat} {bs : List UInt8}
    (hx : Domain x) (hm : s.mems[0]? = some m) (hfit : FiniteAllocator.limit ≤ m.size)
    (hlo : 65536 ≤ q) (hhi : q + bs.length ≤ 65536 + span x)
    (hbytes : ∀ i, i < bs.length → callerByte x (q + i) = bs[i]!) :
    Holds (callerStore s m x) q bs := by
  have hspan : 65536 + span x ≤ m.size := (span_below_heap hx).trans (by
    unfold FiniteAllocator.limit FiniteAllocator.slot₁ FiniteAllocator.slot₀ at hfit
    omega)
  refine holds_fill (s := { s with mems := s.mems.set 0 (metadataMem m) })
    (m := metadataMem m) (setMem_zero hm _) (hhi.trans hspan) hlo hhi ?_
  intro i hi
  rw [show 65536 + (q + i - 65536) = q + i by omega]
  exact hbytes i hi

theorem caller_data {x : Input} {s : Store} {m : MemInst} (hx : Domain x)
    (hm : s.mems[0]? = some m) (hfit : FiniteAllocator.limit ≤ m.size) :
    Data (callerStore s m x) x (layout x) := by
  have hn : 0 < x.n := hx.1
  have hmpos : 0 < x.m := hx.2.1
  have h32 (v : BitVec 32) : (le32 v).length = 4 := by simp [le32]
  have h64 (v : BitVec 64) : (le64 v).length = 8 := by simp [le64, Binary.leBytes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply caller_holds hx hm hfit (by dsimp only [layout]; omega)
    · simp only [List.length_append, h32, layout, span]
      omega
    · intro i hi
      exact caller_dims x (by simpa only [List.length_append, h32] using hi)
  · apply caller_holds hx hm hfit (by dsimp only [layout]; omega)
    · simp only [h32, layout, span]
      omega
    · intro i hi
      exact caller_ptr x (by simpa only [h32] using hi)
  · apply caller_holds hx hm hfit (by dsimp only [layout]; omega)
    · simp only [List.length_append, h32, layout, span]
      omega
    · intro i hi
      exact caller_tag x (by simpa only [List.length_append, h32] using hi)
  · apply caller_holds hx hm hfit (by dsimp only [layout]; omega)
    · simp only [h32, layout, span]
      omega
    · intro i hi
      exact caller_rowsel x (by simpa only [h32] using hi)
  · intro j hj
    apply caller_holds hx hm hfit (by dsimp only [layout]; omega)
    · simp only [h64, layout, span]
      omega
    · intro i hi
      exact caller_lib hj (by simpa only [h64] using hi)
  · intro i hi j hj
    have hb := cell_bound hi hj
    apply caller_holds hx hm hfit (by dsimp only [Layout.cell, layout]; omega)
    · simp only [h64, Layout.cell, layout, span]
      have hs := Nat.mul_le_mul_left 8 hb
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hs ⊢
      omega
    · intro k hk
      exact caller_count hi hj (by simpa only [h64] using hk)

theorem metadata_zero {m : MemInst} {p : Nat}
    (hlo : FiniteAllocator.base ≤ p) (hhi : p + 4 ≤ FiniteAllocator.base + 8) :
    (metadataMem m).read p 4 = 0 := by
  have h : (metadataMem m).read p 4 = 0 % 256 ^ 4 := MemInst.read_of_bytes _ (by
    intro i hi
    have hr : FiniteAllocator.base ≤ p + i ∧ p + i < FiniteAllocator.base + 8 := by omega
    simp only [metadataMem, MemInst.fill, ite_eq_left hr, Nat.zero_div]
    rfl)
  simpa using h

theorem caller_ready {x : Input} {s : Store} {m : MemInst} (hx : Domain x)
    (hm : s.mems[0]? = some m) (hfit : FiniteAllocator.limit ≤ m.size) :
    FiniteAllocator.ready (8 * x.m) 2 (callerStore s m x) := by
  have hb := span_below_heap hx
  have h₀ : FiniteAllocator.size₀ (callerMem m x) = 0 := by
    unfold FiniteAllocator.size₀ callerMem
    rw [read_fill_disjoint _ _ (Or.inr hb)]
    exact metadata_zero (Nat.le_refl _) (by omega)
  have h₁ : FiniteAllocator.size₁ (callerMem m x) = 0 := by
    unfold FiniteAllocator.size₁ callerMem
    rw [read_fill_disjoint _ _ (Or.inr (by omega))]
    exact metadata_zero (by omega) (by omega)
  refine ⟨callerMem m x, caller_mem hm x, hfit, ?_⟩
  rw [h₀, h₁]
  exact Or.inl ⟨rfl, rfl, Nat.le_refl _⟩

theorem caller_linked {x : Input} {s : Store} {m : MemInst} {inst : ModuleInst}
    {a f : Nat} (h : Linked s inst a f) : Linked (callerStore s m x) inst a f := h

theorem layout_outside_heap {x : Input} (hx : Domain x) {a : Nat}
    (h : (layout x).kept x a ∨ (layout x).counts x a) : ¬ FiniteAllocator.heap a := by
  have hb := span_below_heap hx
  dsimp only [Layout.kept, Layout.counts, layout, span] at h hb
  unfold FiniteAllocator.heap
  omega

theorem layout_separate (x : Input) {a : Nat} (h : (layout x).kept x a) :
    ¬ (layout x).counts x a := by
  dsimp only [Layout.kept, Layout.counts, layout] at h ⊢
  omega

theorem layout_bounds {x : Input} (hx : Domain x) :
    (layout x).y + 16 ≤ 2 ^ 32 ∧ (layout x).lib + 32 ≤ 2 ^ 32 ∧
      (layout x).d + 8 * x.m ≤ 2 ^ 32 ∧ (layout x).c + 8 * x.n * x.m ≤ 2 ^ 32 := by
  dsimp only [layout]
  have hb := span_below_heap hx
  unfold span FiniteAllocator.base at hb
  omega

end Subjects.EdgerCpm.Existence
