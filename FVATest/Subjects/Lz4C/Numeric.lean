import FVA.Proof.Lib.BlockNumeric

/-! i32/Nat/Int bridges shared by the decoder proofs. Canonical engine facts stay in
`FVA.Proof.Lib.BlockFacts` + `BlockNumeric`; subject-specific normal forms live here. -/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem igtU_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    igtU (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (decide (b < a)) := by
  simp only [igtU, ofNat32_toNat ha, ofNat32_toNat hb, gt_iff_lt]

-- the literal `2147483648`, never `2 ^ 31`: simp would rewrite the power inside `decide`, leaving
-- an instance no later lemma matches
theorem iltS_zero {a : Nat} (ha : a < 2 ^ 32) :
    iltS (BitVec.ofNat 32 a) (BitVec.ofNat 32 0) = bool (decide (2147483648 ≤ a)) := by
  simp only [iltS, signed, ofNat32_toNat ha, BitVec.toNat_ofNat, Nat.zero_mod]
  congr 1
  simp only [decide_eq_decide]
  split <;> omega

theorem ieq_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ieq (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = bool (a == b) := by
  rw [eq32 ha hb]; congr 1

theorem bool_true : bool true = 1 := rfl
theorem bool_false : bool false = 0 := rfl
theorem one_ne : decide ((1 : BitVec 32) = 0) = false := by decide
theorem zero_eq : decide ((0 : BitVec 32) = 0) = true := by decide

theorem igtU_not {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a + b < 2 ^ 32) :
    igtU (BitVec.ofNat 32 a) (~~~BitVec.ofNat 32 b) = 0 := by
  simp only [igtU, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, gt_iff_lt]
  rw [show decide (2 ^ 32 - 1 - b < a) = false by simp; omega]; rfl

theorem bool_dec_true {p : Prop} [Decidable p] (h : p) : bool (decide p) = 1 := by
  simp [h, bool_true]

theorem bool_dec_false {p : Prop} [Decidable p] (h : ¬ p) : bool (decide p) = 0 := by
  simp [h, bool_false]

theorem ine_ofNat {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ine (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = Num.bool (a != b) := by
  rw [ne32 ha hb]; congr 1

theorem ofNat_ne_zero {k : Nat} (h0 : k ≠ 0) (h : k < 2 ^ 32) :
    decide (BitVec.ofNat 32 k = 0) = false := by
  simpa only [decide_eq_false_iff_not, ofNat32_eq_zero h] using h0

-- Stepping keeps the constructor's `ofNat 0` form; `zero_eq` matches the literal form.
theorem ofNat_zero_eq : decide (BitVec.ofNat 32 0 = 0) = true := zero_eq

theorem toNat_sub_ofNat {x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y).toNat = x - y := by
  rw [ofNat32_sub (by omega) hy, ofNat32_toNat (by omega)]

theorem toNat_add_ofNat {x : BitVec 32} {y : Nat} (h : x.toNat + y < 2 ^ 32) :
    (x + BitVec.ofNat 32 y).toNat = x.toNat + y := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mod_pos {P d : Nat} (h : d ≤ P) (hP : P < 4294967296) :
    (P + 4294967296 - d) % 4294967296 = P - d := by
  rw [show P + 4294967296 - d = P - d + 4294967296 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem mod_neg {P e : Nat} (h : P + e < 4294967296) :
    (P + 4294967296 - (4294967296 - e)) % 4294967296 = P + e := by
  rw [show P + 4294967296 - (4294967296 - e) = P + e by omega, Nat.mod_eq_of_lt h]

/-- The error epilogue's value `~v + src` is negative for `src ≤ v < src + 2^31`. -/
theorem errVal_neg {src v : Nat} (h1 : src ≤ v) (h2 : v < src + 2 ^ 31) :
    (~~~(BitVec.ofNat 32 v) + BitVec.ofNat 32 src).toInt < 0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_toInt {k : Nat} (h : k < 2 ^ 31) : (BitVec.ofNat 32 k).toInt = k := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega

theorem neg1 : (BitVec.ofNat 32 4294967295).toInt < 0 := by decide

theorem sub_mask1 (p : Nat) : BitVec.ofNat 32 p - BitVec.ofNat 32 4294967295 =
    BitVec.ofNat 32 (p + 1) := by
  rw [BitVec.sub_eq_add_neg, show -(BitVec.ofNat 32 4294967295) = BitVec.ofNat 32 1 by decide,
    BitVec.ofNat_add_ofNat]

theorem sub_mask4 (p : Nat) : BitVec.ofNat 32 p - BitVec.ofNat 32 4294967292 =
    BitVec.ofNat 32 (p + 4) := by
  rw [BitVec.sub_eq_add_neg, show -(BitVec.ofNat 32 4294967292) = BitVec.ofNat 32 4 by decide,
    BitVec.ofNat_add_ofNat]

/-- The model's overloaded literal does not match simp's `ofNat`-add pattern. -/
theorem ofNat_add8 (p : Nat) : BitVec.ofNat 32 p + 8 = BitVec.ofNat 32 (p + 8) :=
  BitVec.ofNat_add_ofNat p 8

-- Fold negative constants before footprint reduction: a symbolic `x + c` near `2^32` can
-- drive the kernel into deep recursion instead of exposing the small result `x − k`.
theorem iadd_neg {x c k : Nat} (hc : c + k = 4294967296) (hk : k ≤ x) :
    iadd (BitVec.ofNat 32 x) (BitVec.ofNat 32 c) = BitVec.ofNat 32 (x - k) := by
  have he : c = 2 ^ 32 - k := by omega
  rw [he]
  exact add32_neg hk (by omega)

end Subjects.Lz4C
