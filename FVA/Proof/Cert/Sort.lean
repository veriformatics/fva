import FVA.Impl.Cert.Sort
import Mathlib.Data.Nat.Digits.Lemmas

/-! The `SortedPerm` checker is sound (contract U9 C2). -/

namespace FVA.Cert

namespace Impl

open FVA.Wasm.Binary

theorem intLe_iff (a b : Int) : intLe a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp only [intLe, Nat.ble_eq, Bool.false_eq_true, false_iff,
    true_iff, Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega

theorem intEq_iff (a b : Int) : intEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [intEq]

theorem listEq_iff (as bs : List Int) : listEq as bs = true ↔ as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [listEq]
  | cons a as ih => cases bs <;> simp [listEq, intEq_iff, ih]

theorem insert_perm (x : Int) (l : List Int) : (insert x l).Perm (x :: l) := by
  induction l with
  | nil => simp [insert]
  | cons y ys ih =>
    unfold insert
    cases intLe x y
    · exact ((ih.cons y).trans (List.Perm.swap x y ys))
    · exact List.Perm.refl _

theorem insert_sorted (x : Int) (l : List Int) (h : l.Pairwise (· ≤ ·)) :
    (insert x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [insert]
  | cons y ys ih =>
    unfold insert
    rw [List.pairwise_cons] at h
    cases hxy : intLe x y
    · have hyx : y ≤ x := by have := (intLe_iff x y).not.mp (by simp [hxy]); omega
      simp only [Bool.cond_false, List.pairwise_cons]
      refine ⟨fun z hz => ?_, ih h.2⟩
      rcases List.mem_cons.mp ((insert_perm x ys).mem_iff.mp hz) with rfl | hz
      · exact hyx
      · exact h.1 z hz
    · have hle := (intLe_iff x y).mp hxy
      simp only [Bool.cond_true, List.pairwise_cons]
      refine ⟨fun z hz => ?_, h.1, h.2⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hle
      · exact le_trans hle (h.1 z hz)

theorem isort_perm (xs acc : List Int) : (isort xs acc).Perm (xs ++ acc) := by
  induction xs generalizing acc with
  | nil => simp [isort]
  | cons x xs ih =>
    simp only [isort]
    refine (ih _).trans ?_
    exact ((insert_perm x acc).append_left xs).trans List.perm_middle

theorem isort_sorted (xs acc : List Int) (h : acc.Pairwise (· ≤ ·)) :
    (isort xs acc).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => simpa [isort]
  | cons x xs ih => exact ih _ (insert_sorted x acc h)

/-- `digitsOf` prints `decimal`, given fuel above the digit count. -/
theorem digitsOf_eq (fuel n : Nat) (acc : List UInt8) (h : n < 10 ^ (fuel + 1)) :
    digitsOf (fuel + 1) n acc = decimal n ++ acc := by
  induction fuel generalizing n acc with
  | zero =>
    have hn : n < 10 := by simpa using h
    simp only [digitsOf, Nat.blt_eq.mpr hn, Bool.cond_true]
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · rfl
    · simp [decimal, Nat.ne_of_gt hp, Nat.digits_of_lt 10 n (Nat.ne_of_gt hp) hn]
  | succ f ih =>
    unfold digitsOf
    by_cases hn : n < 10
    · simp only [Nat.blt_eq.mpr hn, Bool.cond_true]
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · rfl
      · simp [decimal, Nat.ne_of_gt hp, Nat.digits_of_lt 10 n (Nat.ne_of_gt hp) hn]
    · have hb : Nat.blt n 10 = false := Bool.eq_false_iff.mpr fun e => hn (Nat.blt_eq.mp e)
      simp only [hb, Bool.cond_false]
      rw [ih (n / 10) _ (by rw [pow_succ] at h; omega)]
      have hn0 : n ≠ 0 := by omega
      have hq0 : n / 10 ≠ 0 := by omega
      simp only [decimal, hn0, hq0, ite_false, Nat.digits_def' (by decide : 1 < 10)
        (Nat.pos_of_ne_zero hn0), List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.singleton_append]

theorem lt_ten_pow_succ (n : Nat) : n < 10 ^ (n + 1) :=
  lt_of_lt_of_le (Nat.lt_pow_self (by decide)) (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))

theorem intText_eq (x : Int) :
    intText x = (if x < 0 then [45] else []) ++ decimal x.natAbs ++ [10] := by
  cases x with
  | ofNat n =>
    rw [intText, digitsOf_eq n n [10] (lt_ten_pow_succ n)]
    simp
  | negSucc n =>
    rw [intText, digitsOf_eq (n + 1) (n + 1) [10] (lt_ten_pow_succ (n + 1))]
    have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    simp [this]

theorem land_255 (v : Nat) : Nat.land v 255 = v % 256 := Nat.and_two_pow_sub_one_eq_mod v 8

/-- `takeBytes` reads its bytes off the front of the packed input. -/
theorem takeBytes_sound {bs : List UInt8} {n v n' v' : Nat}
    (h : takeBytes bs n v = some (n', v')) :
    n = bs.length + n' ∧ leBytes n v = bs ++ leBytes n' v' := by
  induction bs generalizing n v with
  | nil =>
    rw [takeBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons b bs ih =>
    cases n with
    | zero => rw [takeBytes] at h; cases h
    | succ n =>
      rw [takeBytes] at h
      cases hb : Nat.beq b.toNat (Nat.land v 255)
      · rw [hb, Bool.cond_false] at h; cases h
      · rw [hb, Bool.cond_true] at h
        obtain ⟨hn, hl⟩ := ih h
        refine ⟨by rw [hn, List.length_cons]; omega, ?_⟩
        have hbyte : (v % 256).toUInt8 = b := by
          have e : b.toNat = v % 256 := by rw [← land_255]; exact Nat.eq_of_beq_eq_true hb
          apply UInt8.toNat_inj.mp
          rw [e]
          simp
        have hs : Nat.shiftRight v 8 = v / 256 := Nat.shiftRight_eq_div_pow v 8
        rw [hs] at hl
        show (v % 256).toUInt8 :: leBytes n (v / 256) = _
        rw [hbyte, hl]
        rfl

theorem printsAs_sound {xs : List Int} {n v : Nat} (h : printsAs xs n v = true) :
    leBytes n v = IntLines xs := by
  induction xs generalizing n v with
  | nil =>
    simp only [printsAs] at h
    rw [Nat.eq_of_beq_eq_true h]; rfl
  | cons x xs ih =>
    simp only [printsAs] at h
    split at h
    · rename_i n' v' ht
      obtain ⟨_, hl⟩ := takeBytes_sound ht
      rw [hl, ih h, intText_eq]
      simp [IntLines, List.flatMap_cons, List.append_assoc]
    · simp at h

end Impl

open Impl in
theorem SortedPerm.check_sound (i o : Blob) (h : SortedPerm.check i o = true) :
    Accepted SortedPerm i o := by
  unfold SortedPerm.check at h
  split at h
  · rename_i xs ys _ _
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hi, ho⟩, hs⟩ := h
    have hys := (listEq_iff _ _).mp hs
    refine ⟨xs, ys, printsAs_sound hi, printsAs_sound ho, ?_, ?_⟩
    · rw [← hys]; exact isort_sorted xs [] List.Pairwise.nil
    · rw [← hys]; simpa using isort_perm xs []
  · simp at h

end FVA.Cert
