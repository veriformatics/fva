import FVA.Impl.Exec.Chunks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Bitwise

/-!
# Chunked memory denotes the spec memory

Leaf byte arithmetic, the trie's `get`/`set` laws (only the address's low `depth + W` bits
matter), and `MMem.abs` commuting with reads, writes, bulk writes and growth.
-/

namespace FVA.Wasm.Exec.Machine

open FVA.Wasm FVA.Wasm.Exec

namespace Chunks

theorem pow256_pos (i : Nat) : 0 < 256 ^ i := Nat.pow_pos (by norm_num)

theorem leafByte_lt (c i : Nat) : leafByte c i < 256 := Nat.mod_lt _ (by norm_num)

theorem leafSet_div (c i b : Nat) : leafSet c i b / 256 ^ i = b + 256 * (c / 256 ^ (i + 1)) := by
  unfold leafSet
  rw [Nat.add_mul_div_left _ _ (pow256_pos i), Nat.div_eq_of_lt (Nat.mod_lt _ (pow256_pos i)),
    Nat.zero_add]

theorem leafByte_leafSet_self {c i b : Nat} (hb : b < 256) : leafByte (leafSet c i b) i = b := by
  unfold leafByte
  rw [leafSet_div]
  omega

private theorem mod_split (x P R Y : Nat) (hP : 0 < P) :
    (x % (P * (256 * R)) + P * (256 * R) * Y) / P % 256 = x / P % 256 := by
  rw [Nat.mul_assoc P, Nat.add_mul_div_left _ _ hP, Nat.mod_mul_right_div_self,
    Nat.mul_assoc 256, Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd _ (Dvd.intro R rfl)]

theorem leafByte_leafSet_lt {c i j b : Nat} (hj : j < i) :
    leafByte (leafSet c i b) j = leafByte c j := by
  unfold leafByte leafSet
  obtain ⟨k, rfl⟩ : ∃ k, i = j + (k + 1) := ⟨i - j - 1, by omega⟩
  rw [show 256 ^ (j + (k + 1)) = 256 ^ j * (256 * 256 ^ k) by ring]
  exact mod_split _ _ _ _ (pow256_pos j)

private theorem div_split (c i b k : Nat) (hb : b < 256) :
    (c % 256 ^ i + 256 ^ i * (b + 256 * (c / 256 ^ (i + 1)))) / (256 ^ i * (256 * 256 ^ k)) =
      c / (256 ^ (i + 1) * 256 ^ k) := by
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (pow256_pos i),
    Nat.div_eq_of_lt (Nat.mod_lt _ (pow256_pos i)), Nat.zero_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 256), Nat.div_eq_of_lt hb, Nat.zero_add,
    Nat.div_div_eq_div_mul]

theorem leafByte_leafSet_gt {c i j b : Nat} (hb : b < 256) (hj : i < j) :
    leafByte (leafSet c i b) j = leafByte c j := by
  unfold leafByte leafSet
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  rw [show 256 ^ (i + (k + 1)) = 256 ^ i * (256 * 256 ^ k) by ring, div_split _ _ _ _ hb,
    show 256 ^ (i + 1) * 256 ^ k = 256 ^ i * (256 * 256 ^ k) by ring]

theorem leafByte_leafSet_ne {c i j b : Nat} (hb : b < 256) (hj : j ≠ i) :
    leafByte (leafSet c i b) j = leafByte c j := by
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · exact leafByte_leafSet_lt h
  · exact leafByte_leafSet_gt hb h

/-- Leaves only at depth 0. -/
def WF : Nat → Chunks → Prop
  | _, .z => True
  | 0, .leaf _ => True
  | 0, .node _ _ => False
  | _ + 1, .leaf _ => False
  | d + 1, .node l r => WF d l ∧ WF d r

theorem mod_two_pow_eq_iff {a b n : Nat} :
    a % 2 ^ n = b % 2 ^ n ↔ ∀ i < n, a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have := congrArg (Nat.testBit · i) h
    simpa [Nat.testBit_mod_two_pow, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · simp [hi, h i hi]
    · simp [hi]

theorem mod_two_pow_succ_eq_iff {a b k : Nat} :
    a % 2 ^ (k + 1) = b % 2 ^ (k + 1) ↔ a.testBit k = b.testBit k ∧ a % 2 ^ k = b % 2 ^ k := by
  simp only [mod_two_pow_eq_iff]
  constructor
  · intro h
    exact ⟨h k (by omega), fun i hi => h i (by omega)⟩
  · rintro ⟨hk, h⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h i hi
    · exact hk

theorem get_z (d a : Nat) : get d .z a = 0 := by cases d <;> rfl

theorem wf_z (d : Nat) : WF d .z := by cases d <;> trivial

theorem get_lt : ∀ (d : Nat) (t : Chunks) (a : Nat), get d t a < 256
  | _, .z, _ => by simp [get_z]
  | d, .leaf c, a => by cases d <;> exact leafByte_lt _ _
  | 0, .node _ _, _ => by simp [get]
  | d + 1, .node l r, a => by
    simp only [get]
    cases Nat.testBit a (d + W) <;> simp [get_lt d l a, get_lt d r a]

theorem wf_set : ∀ (d : Nat) (t : Chunks) (a b : Nat), WF d t → WF d (set d t a b)
  | 0, _, _, _, _ => by simp [set, WF]
  | d + 1, t, a, b, h => by
    simp only [set]
    cases t with
    | z => cases Nat.testBit a (d + W) <;> simp [WF, wf_set d .z a b (wf_z d), wf_z]
    | leaf => simp [WF] at h
    | node l r =>
      obtain ⟨hl, hr⟩ := h
      cases Nat.testBit a (d + W) <;> simp [WF, wf_set d l a b hl, wf_set d r a b hr, hl, hr]

private theorem leafByte_leafSet_mod (c a b a' : Nat) (hb : b < 256) :
    leafByte (leafSet c (a % 2 ^ W) b) (a' % 2 ^ W) =
      if a' % 2 ^ W = a % 2 ^ W then b else leafByte c (a' % 2 ^ W) := by
  split_ifs with he
  · rw [he, leafByte_leafSet_self hb]
  · exact leafByte_leafSet_ne hb he

theorem get_set : ∀ (d : Nat) (t : Chunks) (a b a' : Nat), WF d t → b < 256 →
    get d (set d t a b) a' = if a' % 2 ^ (d + W) = a % 2 ^ (d + W) then b else get d t a'
  | 0, t, a, b, a', h, hb => by
    cases t with
    | z =>
      simp only [set, get, Nat.zero_add, leafByte_leafSet_mod _ _ _ _ hb]
      simp [leafByte]
    | leaf c => simp only [set, get, Nat.zero_add, leafByte_leafSet_mod _ _ _ _ hb]
    | node => simp [WF] at h
  | d + 1, t, a, b, a', h, hb => by
    have hsplit : a' % 2 ^ (d + 1 + W) = a % 2 ^ (d + 1 + W) ↔
        a'.testBit (d + W) = a.testBit (d + W) ∧ a' % 2 ^ (d + W) = a % 2 ^ (d + W) := by
      rw [show d + 1 + W = d + W + 1 by omega]
      exact mod_two_pow_succ_eq_iff
    obtain ⟨l, r, hl, hr, hget, hset⟩ : ∃ l r, WF d l ∧ WF d r ∧
        (∀ x, get (d + 1) t x = bif Nat.testBit x (d + W) then get d r x else get d l x) ∧
        (set (d + 1) t a b = bif Nat.testBit a (d + W) then .node l (set d r a b)
          else .node (set d l a b) r) := by
      cases t with
      | z => exact ⟨.z, .z, wf_z d, wf_z d, fun x => by
          cases Nat.testBit x (d + W) <;> simp [get_z], by simp [set]⟩
      | leaf => simp [WF] at h
      | node l r => exact ⟨l, r, h.1, h.2, fun x => rfl, by simp [set]⟩
    rw [hset, hget a']
    have ihl := get_set d l a b a' hl hb
    have ihr := get_set d r a b a' hr hb
    by_cases hc : a' % 2 ^ (d + 1 + W) = a % 2 ^ (d + 1 + W)
    · obtain ⟨hbit, hlow⟩ := hsplit.mp hc
      simp only [hc, ↓reduceIte]
      cases ha : Nat.testBit a (d + W) <;> simp only [ha] at hbit <;>
        simp [get, hbit, ihl, ihr, hlow]
    · simp only [hc, ↓reduceIte]
      by_cases hbit : a'.testBit (d + W) = a.testBit (d + W)
      · have hlow : a' % 2 ^ (d + W) ≠ a % 2 ^ (d + W) := fun h' => hc (hsplit.mpr ⟨hbit, h'⟩)
        cases ha : Nat.testBit a (d + W) <;> simp only [ha] at hbit <;>
          simp [get, hbit, ihl, ihr, hlow]
      · cases ha : Nat.testBit a (d + W) <;> cases ha' : Nat.testBit a' (d + W) <;>
          simp_all [get]

end Chunks

namespace MMem

/-- The trie is well formed at the memory's depth. -/
def WF (m : MMem) : Prop := Chunks.WF m.depth m.data

/-- The trie reaches every address below the size. -/
def Cover (m : MMem) : Prop := m.size ≤ 2 ^ (m.depth + W)

/-- Bytes at and past the size are zero. -/
def ZeroTail (m : MMem) : Prop := ∀ a, m.size ≤ a → m.byte a = 0

/-- The machine memory invariant. -/
def Inv (m : MMem) : Prop := m.WF ∧ m.Cover ∧ m.ZeroTail ∧ m.pages ≤ 2 ^ 16

theorem byte_lt (m : MMem) (a : Nat) : m.byte a < 256 := by
  unfold byte
  cases Nat.blt a (2 ^ (m.depth + W)) <;> simp [Chunks.get_lt]

theorem byte_setData {m : MMem} {a b : Nat} (hw : m.WF) (ha : a < 2 ^ (m.depth + W))
    (hb : b < 256) (a' : Nat) :
    ({ m with data := m.data.set m.depth a b } : MMem).byte a' =
      if a' = a then b else m.byte a' := by
  unfold byte
  simp only
  by_cases h' : a' < 2 ^ (m.depth + W)
  · have hbl : a'.blt (2 ^ (m.depth + W)) = true := by simpa [Nat.blt_eq] using h'
    simp only [hbl, Bool.cond_true, Chunks.get_set _ _ _ _ _ hw hb, Nat.mod_eq_of_lt h',
      Nat.mod_eq_of_lt ha]
  · have hne : a' ≠ a := by omega
    simp [Nat.blt_eq, h', hne]

theorem wf_setData {m : MMem} {a b : Nat} (hw : m.WF) :
    ({ m with data := m.data.set m.depth a b } : MMem).WF := Chunks.wf_set _ _ _ _ hw

theorem write_fields (m : MMem) (ea k v : Nat) :
    (m.write ea k v).pages = m.pages ∧ (m.write ea k v).max = m.max ∧
      (m.write ea k v).depth = m.depth := by
  induction k generalizing m ea v with
  | zero => simp [write]
  | succ k ih =>
    have h := ih { m with data := m.data.set m.depth ea (v % 256) } (ea + 1) (v / 256)
    simpa only [write] using h

theorem write_wf {m : MMem} (hw : m.WF) (ea k v : Nat) : (m.write ea k v).WF := by
  induction k generalizing m ea v with
  | zero => exact hw
  | succ k ih => exact ih (wf_setData hw) _ _

theorem byte_write {m : MMem} (hw : m.WF) {ea k : Nat} (hk : ea + k ≤ 2 ^ (m.depth + W))
    (v a : Nat) :
    (m.write ea k v).byte a =
      if ea ≤ a ∧ a < ea + k then v / 256 ^ (a - ea) % 256 else m.byte a := by
  induction k generalizing m ea v with
  | zero =>
    have h : ¬ (ea ≤ a ∧ a < ea + 0) := by omega
    simp only [write, h, ↓reduceIte]
  | succ k ih =>
    simp only [write]
    rw [ih (wf_setData hw) (by simpa using (show ea + 1 + k ≤ 2 ^ (m.depth + W) by omega)),
      byte_setData hw (by omega) (Nat.mod_lt _ (by norm_num))]
    by_cases h1 : ea + 1 ≤ a ∧ a < ea + 1 + k
    · have h1' : ea ≤ a ∧ a < ea + (k + 1) := by omega
      simp only [h1, h1', and_self, ↓reduceIte]
      rw [Nat.div_div_eq_div_mul, show a - ea = (a - (ea + 1)) + 1 by omega, Nat.pow_succ,
        Nat.mul_comm (256 ^ _) 256]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : a = ea
      · subst h2; simp
      · have h2' : ¬ (ea ≤ a ∧ a < ea + (k + 1)) := by omega
        simp only [h2, h2', ↓reduceIte]

theorem write_inv {m : MMem} (hi : m.Inv) {ea k : Nat} (hk : ea + k ≤ m.size) (v : Nat) :
    (m.write ea k v).Inv := by
  obtain ⟨hw, hc, hz, hpg⟩ := hi
  obtain ⟨hp, -, hd⟩ := write_fields m ea k v
  have hc' : ea + k ≤ 2 ^ (m.depth + W) := by simp only [Cover, size] at hc hk; omega
  refine ⟨write_wf hw _ _ _, ?_, ?_, by rw [hp]; exact hpg⟩
  · simp only [Cover, size] at hc ⊢; rw [hp, hd]; exact hc
  · intro a ha
    simp only [size] at ha hk; rw [hp] at ha
    have hn : ¬ (ea ≤ a ∧ a < ea + k) := by omega
    rw [byte_write hw hc']
    simp only [hn, ↓reduceIte]
    exact hz a (by simp only [size]; omega)

theorem abs_read (m : MMem) (ea k : Nat) : m.abs.read ea k = m.read ea k := by
  induction k generalizing ea with
  | zero => rfl
  | succ k ih =>
    simp only [MemInst.read, read, ih]
    simp [abs, Nat.mod_eq_of_lt (byte_lt m ea)]

theorem writeBytes_fields (m : MMem) (dst : Nat) (bs : List Nat) :
    (m.writeBytes dst bs).pages = m.pages ∧ (m.writeBytes dst bs).max = m.max ∧
      (m.writeBytes dst bs).depth = m.depth := by
  induction bs generalizing m dst with
  | nil => simp [writeBytes]
  | cons b bs ih =>
    have h := ih { m with data := m.data.set m.depth dst b } (dst + 1)
    simpa only [writeBytes] using h

theorem writeBytes_wf {m : MMem} (hw : m.WF) (dst : Nat) (bs : List Nat) :
    (m.writeBytes dst bs).WF := by
  induction bs generalizing m dst with
  | nil => exact hw
  | cons b bs ih => exact ih (wf_setData hw) _

theorem byte_writeBytes {m : MMem} (hw : m.WF) {dst : Nat} {bs : List Nat}
    (hk : dst + bs.length ≤ 2 ^ (m.depth + W)) (hb : ∀ b ∈ bs, b < 256) (a : Nat) :
    (m.writeBytes dst bs).byte a =
      if dst ≤ a ∧ a < dst + bs.length then bs.getD (a - dst) 0 else m.byte a := by
  induction bs generalizing m dst with
  | nil =>
    have h : ¬ (dst ≤ a ∧ a < dst + ([] : List Nat).length) := by simp
    simp only [writeBytes, h, ↓reduceIte]
  | cons b bs ih =>
    simp only [writeBytes]
    have hk' : dst + 1 + bs.length ≤
        2 ^ (({ m with data := m.data.set m.depth dst b } : MMem).depth + W) := by
      simp only [List.length_cons] at hk; simpa using (show dst + 1 + bs.length ≤ _ by omega)
    rw [ih (wf_setData hw) hk' (fun x hx => hb x (List.mem_cons_of_mem _ hx)),
      byte_setData hw (by simp only [List.length_cons] at hk; omega) (hb b (List.mem_cons_self ..))]
    by_cases h1 : dst + 1 ≤ a ∧ a < dst + 1 + bs.length
    · have h1' : dst ≤ a ∧ a < dst + (b :: bs).length := by simp only [List.length_cons]; omega
      simp only [h1, h1', and_self, ↓reduceIte]
      rw [show a - dst = (a - (dst + 1)) + 1 by omega]
      simp
    · simp only [h1, ↓reduceIte]
      by_cases h2 : a = dst
      · subst h2; simp
      · have h2' : ¬ (dst ≤ a ∧ a < dst + (b :: bs).length) := by
          simp only [List.length_cons]; omega
        simp only [h2, h2', ↓reduceIte]

theorem writeBytes_inv {m : MMem} (hi : m.Inv) {dst : Nat} {bs : List Nat}
    (hk : dst + bs.length ≤ m.size) (hb : ∀ b ∈ bs, b < 256) : (m.writeBytes dst bs).Inv := by
  obtain ⟨hw, hc, hz, hpg⟩ := hi
  obtain ⟨hp, -, hd⟩ := writeBytes_fields m dst bs
  have hc' : dst + bs.length ≤ 2 ^ (m.depth + W) := by simp only [Cover, size] at hc hk; omega
  refine ⟨writeBytes_wf hw _ _, ?_, ?_, by rw [hp]; exact hpg⟩
  · simp only [Cover, size] at hc ⊢; rw [hp, hd]; exact hc
  · intro a ha
    simp only [size] at ha hk; rw [hp] at ha
    have hn : ¬ (dst ≤ a ∧ a < dst + bs.length) := by omega
    rw [byte_writeBytes hw hc' hb]
    simp only [hn, ↓reduceIte]
    exact hz a (by simp only [size]; omega)

theorem readBytes_length (m : MMem) (src n : Nat) : (m.readBytes src n).length = n := by
  induction n generalizing src with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

theorem readBytes_getD (m : MMem) (src n i : Nat) (hi : i < n) :
    (m.readBytes src n).getD i 0 = m.byte (src + i) := by
  induction n generalizing src i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [readBytes]
    | succ i =>
      simp only [readBytes, List.getD_cons_succ]
      rw [ih (src + 1) i (by omega), show src + 1 + i = src + (i + 1) by omega]

theorem readBytes_lt (m : MMem) (src n : Nat) : ∀ b ∈ m.readBytes src n, b < 256 := by
  induction n generalizing src with
  | zero => simp [readBytes]
  | succ n ih =>
    intro b hb
    simp only [readBytes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact byte_lt m src
    · exact ih _ b hb

theorem depthFor_cover : ∀ (fuel n : Nat), n ≤ 2 ^ (fuel + W) → n ≤ 2 ^ (depthFor n fuel + W)
  | 0, n, h => by simpa [depthFor] using h
  | fuel + 1, n, h => by
    simp only [depthFor]
    cases hb : Nat.ble n (2 ^ W) with
    | true => simpa using Nat.le_of_ble_eq_true hb
    | false =>
      simp only [Bool.cond_false]
      have h2 : (n + 1) / 2 ≤ 2 ^ (fuel + W) := by
        rw [show fuel + 1 + W = (fuel + W) + 1 by omega, Nat.pow_succ] at h
        omega
      have ih := depthFor_cover fuel ((n + 1) / 2) h2
      rw [show depthFor ((n + 1) / 2) fuel + 1 + W = (depthFor ((n + 1) / 2) fuel + W) + 1 by omega,
        Nat.pow_succ]
      omega

theorem deepen_fields (m : MMem) (k : Nat) :
    (m.deepen k).pages = m.pages ∧ (m.deepen k).max = m.max ∧
      (m.deepen k).depth = m.depth + k := by
  induction k generalizing m with
  | zero => simp [deepen]
  | succ k ih =>
    have h := ih { m with depth := m.depth + 1, data := .node m.data .z }
    simp only [deepen] at h ⊢
    exact ⟨h.1, h.2.1, by omega⟩

theorem deepen_wf {m : MMem} (hw : m.WF) (k : Nat) : (m.deepen k).WF := by
  induction k generalizing m with
  | zero => exact hw
  | succ k ih => exact ih (show Chunks.WF (m.depth + 1) (.node m.data .z) from ⟨hw, Chunks.wf_z _⟩)

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa [Nat.blt_eq] using h

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hb) (by omega)

theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  by_cases h : a < b
  · simp [h, blt_true h]
  · simp [h, blt_false (by omega : b ≤ a)]

theorem byte_node_z (m : MMem) (a : Nat) :
    ({ m with depth := m.depth + 1, data := .node m.data .z } : MMem).byte a = m.byte a := by
  unfold byte
  simp only
  by_cases h1 : a < 2 ^ (m.depth + W)
  · have h2 : a < 2 ^ (m.depth + 1 + W) := lt_of_lt_of_le h1
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb : a.testBit (m.depth + W) = false := Nat.testBit_eq_false_of_lt h1
    simp [blt_true h1, blt_true h2, Chunks.get, hb]
  · rw [blt_false (by omega : 2 ^ (m.depth + W) ≤ a)]
    by_cases h2 : a < 2 ^ (m.depth + 1 + W)
    · have e2 := blt_true h2
      obtain ⟨x, rfl⟩ : ∃ x, a = 2 ^ (m.depth + W) + x := ⟨a - 2 ^ (m.depth + W), by omega⟩
      have hx : x < 2 ^ (m.depth + W) := by
        rw [show m.depth + 1 + W = (m.depth + W) + 1 by omega, Nat.pow_succ] at h2; omega
      have hb : (2 ^ (m.depth + W) + x).testBit (m.depth + W) = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hx]; rfl
      simp [e2, Chunks.get, hb, Chunks.get_z]
    · simp [blt_false (by omega : 2 ^ (m.depth + 1 + W) ≤ a)]

theorem byte_deepen (m : MMem) (k a : Nat) : (m.deepen k).byte a = m.byte a := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    simp only [deepen]
    rw [ih, byte_node_z]

theorem grow_cond (m : MMem) (n : Nat) :
    (Nat.blt (2 ^ 16) (m.pages + n) || m.max.any (Nat.blt · (m.pages + n))) =
      decide (2 ^ 16 < m.pages + n ∨ (m.max.any fun x => decide (x < m.pages + n)) = true) := by
  rcases m with ⟨p, mx, d, dt⟩
  cases mx <;> simp [blt_eq_decide]

theorem grow_eq (m : MMem) (n : Nat) : m.grow n =
    if 2 ^ 16 < m.pages + n ∨ (m.max.any fun x => decide (x < m.pages + n)) = true then none
    else some ({ m with pages := m.pages + n }.deepen
      (depthFor ((m.pages + n) * 65536) 64 - m.depth)) := by
  simp only [grow, grow_cond, Bool.cond_decide]

theorem abs_grow (m : MMem) (n : Nat) : m.abs.grow n =
    if 2 ^ 16 < m.pages + n ∨ (m.max.any fun x => decide (x < m.pages + n)) = true then none
    else some (MemInst.mk (m.pages + n) m.max fun a =>
      if a < m.size then UInt8.ofNat (m.byte a) else 0) := rfl

theorem grow_none {m : MMem} {n : Nat} : m.grow n = none ↔ m.abs.grow n = none := by
  rw [grow_eq, abs_grow]
  split_ifs <;> simp

theorem grow_some {m : MMem} (hi : m.Inv) {n : Nat} {m' : MMem} (h : m.grow n = some m') :
    m'.Inv ∧ m.abs.grow n = some m'.abs := by
  obtain ⟨hw, hc, hz, -⟩ := hi
  rw [grow_eq] at h
  split at h
  · contradiction
  · next hcond =>
    simp only [Option.some.injEq] at h
    subst h
    have hlen : m.pages + n ≤ 2 ^ 16 := by omega
    obtain ⟨hp, hmx, hd⟩ := deepen_fields { m with pages := m.pages + n }
      (depthFor ((m.pages + n) * 65536) 64 - m.depth)
    have hcov := depthFor_cover 64 ((m.pages + n) * 65536)
      (by calc (m.pages + n) * 65536 ≤ 2 ^ 16 * 65536 := Nat.mul_le_mul_right _ hlen
            _ ≤ 2 ^ (64 + W) := by norm_num [W])
    refine ⟨⟨deepen_wf (m := { m with pages := m.pages + n }) hw _, ?_, ?_,
      by rw [hp]; exact hlen⟩, ?_⟩
    · simp only [Cover, size, hp, hd]
      exact le_trans hcov (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro a ha
      simp only [size, hp] at ha
      rw [byte_deepen]
      exact hz a (by simp only [size]; nlinarith)
    · rw [abs_grow]
      simp only [hcond, ↓reduceIte, Option.some.injEq]
      simp only [abs, hp, hmx]
      congr 1
      funext a
      rw [byte_deepen]
      have hbyte : ({ m with pages := m.pages + n } : MMem).byte a = m.byte a := rfl
      by_cases ha : a < m.size
      · simp only [ha, ↓reduceIte, hbyte]
      · simp only [ha, ↓reduceIte, hbyte, hz a (by omega)]
        rfl

theorem alloc_abs (p : Nat) (mx : Option Nat) :
    (alloc p mx).abs = { pages := p, max := mx, byte := fun _ => 0 } := by
  simp only [abs, alloc, byte, Chunks.get_z]
  congr 1
  funext a
  cases Nat.blt a _ <;> rfl

theorem alloc_inv (p : Nat) (mx : Option Nat) (hp : p ≤ 2 ^ 16) : (alloc p mx).Inv := by
  refine ⟨Chunks.wf_z _, ?_, ?_, hp⟩
  · simp only [Cover, size, alloc]
    exact depthFor_cover 64 _ (by
      calc p * 65536 ≤ 2 ^ 16 * 65536 := Nat.mul_le_mul_right _ hp
        _ ≤ 2 ^ (64 + W) := by norm_num [W])
  · intro a _
    simp only [byte, alloc, Chunks.get_z]
    cases Nat.blt a _ <;> rfl

theorem abs_ext {m₁ m₂ : MMem} (hp : m₁.pages = m₂.pages) (hm : m₁.max = m₂.max)
    (hb : ∀ a, m₁.byte a = m₂.byte a) : m₁.abs = m₂.abs := by
  simp only [abs, hp, hm]
  congr 1
  funext a
  rw [hb]

theorem abs_write {m : MMem} (hw : m.WF) {ea k : Nat} (hk : ea + k ≤ 2 ^ (m.depth + W))
    (v : Nat) : (m.write ea k v).abs = m.abs.write ea k v := by
  obtain ⟨hp, hm, -⟩ := write_fields m ea k v
  simp only [abs, MemInst.write, hp, hm]
  congr 1
  funext a
  rw [byte_write hw hk]
  split_ifs
  · exact UInt8.ofNat_mod_size
  · rfl

end MMem

end FVA.Wasm.Exec.Machine
