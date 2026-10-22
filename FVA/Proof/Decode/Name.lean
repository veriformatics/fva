import FVA.Proof.Decode.Reader
import Init.Data.String.Basic

/-!
# UTF-8 names

The byte decoder accepts exactly the UTF-8 encoding used by the binary grammar's `Name`.
The fuel bound is the byte count; every decoded scalar consumes at least one byte.
-/

namespace FVA.Wasm.Decode

open FVA.Wasm.Binary

/-- The list form of Lean's UTF-8 encoding. -/
def utf8Bytes (cs : List Char) : List UInt8 := cs.flatMap String.utf8EncodeChar

@[simp] theorem utf8Bytes_nil : utf8Bytes [] = [] := rfl

@[simp] theorem utf8Bytes_cons (c : Char) (cs : List Char) :
    utf8Bytes (c :: cs) = String.utf8EncodeChar c ++ utf8Bytes cs := by
  simp [utf8Bytes]

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have h : ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r hi ih =>
      rw [ih, List.reverse_cons, List.append_assoc]
      congr 1
      rw [List.drop_eq_getElem_cons (i := i) (by simpa using hi)]
      simp [ByteArray.get!, hi]
    | case2 i r hi =>
      have he : bs.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
      simp [he]
  simpa [ByteArray.toList] using h 0 []

theorem utf8Bytes_ofList (cs : List Char) :
    (String.ofList cs).toUTF8.toList = utf8Bytes cs := by
  simp [String.toUTF8_eq_toByteArray, List.utf8Encode, utf8Bytes, byteArray_toList]

theorem utf8Bytes_toList (s : String) : utf8Bytes s.toList = s.toUTF8.toList := by
  rw [← utf8Bytes_ofList, String.ofList_toList]

theorem charOfNat_toNat {n : Nat} (hn : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp only [Char.ofNat, dite_eq_left hn]
  rfl

theorem land_pack (a : UInt8) (bs : List UInt8) : pack (a :: bs) &&& 255 = a.toNat :=
  land_pack_cons a bs

theorem shift_pack_8 (a : UInt8) (bs : List UInt8) : pack (a :: bs) >>> 8 = pack bs :=
  shiftRight_pack_cons a bs

theorem shift_pack_16 (a b : UInt8) (bs : List UInt8) :
    pack (a :: b :: bs) >>> 16 = pack bs := by
  rw [show 16 = 8 + 8 from rfl, Nat.shiftRight_add]
  change Nat.shiftRight (Nat.shiftRight (pack (a :: b :: bs)) 8) 8 = _
  rw [shiftRight_pack_cons, shiftRight_pack_cons]

theorem shift_pack_24 (a b c : UInt8) (bs : List UInt8) :
    pack (a :: b :: c :: bs) >>> 24 = pack bs := by
  rw [show 24 = 16 + 8 from rfl, Nat.shiftRight_add, shift_pack_16]
  exact shiftRight_pack_cons c bs

theorem shift_pack_32 (a b c d : UInt8) (bs : List UInt8) :
    pack (a :: b :: c :: d :: bs) >>> 32 = pack bs := by
  rw [show 32 = 24 + 8 from rfl, Nat.shiftRight_add, shift_pack_24]
  exact shiftRight_pack_cons d bs

theorem cont_true {b : Nat} : cont b = true ↔ 128 ≤ b ∧ b < 192 := by
  simp [cont]

theorem encode_one (a : UInt8) (ha : a.toNat < 128) :
    String.utf8EncodeChar (Char.ofNat a.toNat) = [a] := by
  have hv : a.toNat.isValidChar := Or.inl (by omega)
  simp only [String.utf8EncodeChar, Char.toNat_val, charOfNat_toNat hv,
    ite_eq_left (show a.toNat ≤ 127 by omega), UInt8.ofNat_toNat]

theorem encode_two (a b : UInt8) (ha : 194 ≤ a.toNat ∧ a.toNat < 224)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) :
    String.utf8EncodeChar (Char.ofNat ((a.toNat - 192) * 64 + (b.toNat - 128))) = [a, b] := by
  have hv : ((a.toNat - 192) * 64 + (b.toNat - 128)).isValidChar := Or.inl (by omega)
  simp only [String.utf8EncodeChar, Char.toNat_val, charOfNat_toNat hv,
    ite_eq_right (by omega : ¬(a.toNat - 192) * 64 + (b.toNat - 128) ≤ 127),
    ite_eq_left (by omega : (a.toNat - 192) * 64 + (b.toNat - 128) ≤ 2047),
    List.cons.injEq, and_true, ← UInt8.toNat_inj, UInt8.toNat_ofNat']
  omega

theorem encode_three (a b c : UInt8) (ha : 224 ≤ a.toNat ∧ a.toNat < 240)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hmin : 2048 ≤ (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128))
    (hvalid : (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128) < 55296 ∨
      57344 ≤ (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)) :
    String.utf8EncodeChar (Char.ofNat
      ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128))) = [a, b, c] := by
  have hv : ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)).isValidChar := by
    unfold Nat.isValidChar
    omega
  simp only [String.utf8EncodeChar, Char.toNat_val, charOfNat_toNat hv,
    ite_eq_right (by omega :
      ¬(a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128) ≤ 127),
    ite_eq_right (by omega :
      ¬(a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128) ≤ 2047),
    ite_eq_left (by omega :
      (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128) ≤ 65535),
    List.cons.injEq, and_true, ← UInt8.toNat_inj, UInt8.toNat_ofNat']
  omega

theorem encode_four (a b c d : UInt8) (ha : 240 ≤ a.toNat ∧ a.toNat < 245)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hd : 128 ≤ d.toNat ∧ d.toNat < 192)
    (hmin : 65536 ≤ (a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128))
    (hmax : (a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128) < 1114112) :
    String.utf8EncodeChar (Char.ofNat ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128))) = [a, b, c, d] := by
  have hv : ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128)).isValidChar := Or.inr ⟨by omega, hmax⟩
  simp only [String.utf8EncodeChar, Char.toNat_val, charOfNat_toNat hv,
    ite_eq_right (by omega : ¬(a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128) ≤ 127),
    ite_eq_right (by omega : ¬(a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128) ≤ 2047),
    ite_eq_right (by omega : ¬(a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128) ≤ 65535),
    List.cons.injEq, and_true, ← UInt8.toNat_inj, UInt8.toNat_ofNat']
  omega

theorem utf8_one (fuel : Nat) (a : UInt8) (bs : List UInt8) (ha : a.toNat < 128) :
    utf8 (fuel + 1) (pack (a :: bs)) (a :: bs).length =
      (utf8 fuel (pack bs) bs.length).bind fun cs v n => .ok (Char.ofNat a.toNat :: cs) v n := by
  simp only [utf8, List.length_cons, land_pack, blt_true.2 ha, Bool.cond_true,
    Nat.reduceMul, shift_pack_8, Nat.add_sub_cancel]

theorem utf8_two (fuel : Nat) (a b : UInt8) (bs : List UInt8)
    (ha : 194 ≤ a.toNat ∧ a.toNat < 224) (hb : 128 ≤ b.toNat ∧ b.toNat < 192) :
    utf8 (fuel + 1) (pack (a :: b :: bs)) (a :: b :: bs).length =
      (utf8 fuel (pack bs) bs.length).bind fun cs v n =>
        .ok (Char.ofNat ((a.toNat - 192) * 64 + (b.toNat - 128)) :: cs) v n := by
  have h1 : Nat.blt a.toNat 128 = false := blt_false.2 (by omega)
  have h2 : Nat.blt a.toNat 194 = false := blt_false.2 ha.1
  have h3 : Nat.blt a.toNat 224 = true := blt_true.2 ha.2
  have hl : Nat.ble 2 (bs.length + 1 + 1) = true := ble_true.2 (by omega)
  simp only [utf8, List.length_cons, land_pack, shift_pack_8, h1, h2, h3,
    Bool.cond_false, Bool.cond_true, hl, cont_true.2 hb, Bool.and_self, Nat.reduceMul,
    shift_pack_16, show bs.length + 1 + 1 - 2 = bs.length by omega]

theorem utf8_three (fuel : Nat) (a b c : UInt8) (bs : List UInt8)
    (ha : 224 ≤ a.toNat ∧ a.toNat < 240) (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hmin : 2048 ≤ (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128))
    (hvalid : (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128) < 55296 ∨
      57344 ≤ (a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)) :
    utf8 (fuel + 1) (pack (a :: b :: c :: bs)) (a :: b :: c :: bs).length =
      (utf8 fuel (pack bs) bs.length).bind fun cs v n => .ok
        (Char.ofNat ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)) :: cs)
        v n := by
  have h1 : Nat.blt a.toNat 128 = false := blt_false.2 (by omega)
  have h2 : Nat.blt a.toNat 194 = false := blt_false.2 (by omega)
  have h3 : Nat.blt a.toNat 224 = false := blt_false.2 ha.1
  have h4 : Nat.blt a.toNat 240 = true := blt_true.2 ha.2
  have hl : Nat.ble 3 (bs.length + 1 + 1 + 1) = true := ble_true.2 (by omega)
  have hv : (Nat.blt ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)) 55296 ||
      Nat.ble 57344 ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128))) = true := by
    simpa using hvalid
  simp only [utf8, List.length_cons, land_pack, shift_pack_8, shift_pack_16, h1, h2, h3, h4,
    Bool.cond_false, Bool.cond_true, hl, cont_true.2 hb, cont_true.2 hc, ble_true.2 hmin, hv,
    Bool.and_self, Nat.reduceMul, shift_pack_24,
    show bs.length + 1 + 1 + 1 - 3 = bs.length by omega]

theorem utf8_four (fuel : Nat) (a b c d : UInt8) (bs : List UInt8)
    (ha : 240 ≤ a.toNat ∧ a.toNat < 245) (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
    (hc : 128 ≤ c.toNat ∧ c.toNat < 192) (hd : 128 ≤ d.toNat ∧ d.toNat < 192)
    (hmin : 65536 ≤ (a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128))
    (hmax : (a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
      (c.toNat - 128) * 64 + (d.toNat - 128) < 1114112) :
    utf8 (fuel + 1) (pack (a :: b :: c :: d :: bs)) (a :: b :: c :: d :: bs).length =
      (utf8 fuel (pack bs) bs.length).bind fun cs v n => .ok (Char.ofNat
        ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 +
          (c.toNat - 128) * 64 + (d.toNat - 128)) :: cs) v n := by
  have h1 : Nat.blt a.toNat 128 = false := blt_false.2 (by omega)
  have h2 : Nat.blt a.toNat 194 = false := blt_false.2 (by omega)
  have h3 : Nat.blt a.toNat 224 = false := blt_false.2 (by omega)
  have h4 : Nat.blt a.toNat 240 = false := blt_false.2 ha.1
  have h5 : Nat.blt a.toNat 245 = true := blt_true.2 ha.2
  have hl : Nat.ble 4 (bs.length + 1 + 1 + 1 + 1) = true := ble_true.2 (by omega)
  simp only [utf8, List.length_cons, land_pack, shift_pack_8, shift_pack_16, shift_pack_24,
    h1, h2, h3, h4, h5, Bool.cond_false, Bool.cond_true, hl, cont_true.2 hb, cont_true.2 hc,
    cont_true.2 hd, ble_true.2 hmin, blt_true.2 hmax, Bool.and_self, Nat.reduceMul, shift_pack_32,
    show bs.length + 1 + 1 + 1 + 1 - 4 = bs.length by omega]

theorem byteOfNat_toNat {n : Nat} (hn : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem utf8_char (fuel : Nat) (c : Char) (bs : List UInt8) :
    utf8 (fuel + 1) (pack (String.utf8EncodeChar c ++ bs))
      (String.utf8EncodeChar c ++ bs).length =
      (utf8 fuel (pack bs) bs.length).bind fun cs v n => .ok (c :: cs) v n := by
  have hv : c.toNat.isValidChar := c.valid
  have hmax : c.toNat < 1114112 := by unfold Nat.isValidChar at hv; omega
  by_cases h1 : c.toNat ≤ 127
  · simp only [String.utf8EncodeChar, Char.toNat_val, ite_eq_left h1,
      List.cons_append, List.nil_append]
    have ha := byteOfNat_toNat (n := c.toNat) (by omega)
    rw [utf8_one fuel _ bs (by rw [ha]; omega), ha, Char.ofNat_toNat]
  · by_cases h2 : c.toNat ≤ 2047
    · simp only [String.utf8EncodeChar, Char.toNat_val, ite_eq_right h1, ite_eq_left h2,
        List.cons_append, List.nil_append]
      have ha := byteOfNat_toNat (n := c.toNat / 64 % 32 + 192) (by omega)
      have hb := byteOfNat_toNat (n := c.toNat % 64 + 128) (by omega)
      rw [utf8_two fuel _ _ bs (by rw [ha]; omega) (by rw [hb]; omega), ha, hb,
        show (c.toNat / 64 % 32 + 192 - 192) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat
          by omega, Char.ofNat_toNat]
    · by_cases h3 : c.toNat ≤ 65535
      · simp only [String.utf8EncodeChar, Char.toNat_val, ite_eq_right h1, ite_eq_right h2,
          ite_eq_left h3, List.cons_append, List.nil_append]
        have ha := byteOfNat_toNat (n := c.toNat / 4096 % 16 + 224) (by omega)
        have hb := byteOfNat_toNat (n := c.toNat / 64 % 64 + 128) (by omega)
        have hc := byteOfNat_toNat (n := c.toNat % 64 + 128) (by omega)
        have he : (c.toNat / 4096 % 16 + 224 - 224) * 4096 +
            (c.toNat / 64 % 64 + 128 - 128) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat := by
          omega
        rw [utf8_three fuel _ _ _ bs (by rw [ha]; omega) (by rw [hb]; omega)
          (by rw [hc]; omega) (by rw [ha, hb, hc, he]; omega)
          (by rw [ha, hb, hc, he]; unfold Nat.isValidChar at hv; omega),
          ha, hb, hc, he, Char.ofNat_toNat]
      · simp only [String.utf8EncodeChar, Char.toNat_val, ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h3, List.cons_append, List.nil_append]
        have ha := byteOfNat_toNat (n := c.toNat / 262144 % 8 + 240) (by omega)
        have hb := byteOfNat_toNat (n := c.toNat / 4096 % 64 + 128) (by omega)
        have hc := byteOfNat_toNat (n := c.toNat / 64 % 64 + 128) (by omega)
        have hd := byteOfNat_toNat (n := c.toNat % 64 + 128) (by omega)
        have he : (c.toNat / 262144 % 8 + 240 - 240) * 262144 +
            (c.toNat / 4096 % 64 + 128 - 128) * 4096 +
            (c.toNat / 64 % 64 + 128 - 128) * 64 + (c.toNat % 64 + 128 - 128) = c.toNat := by
          omega
        rw [utf8_four fuel _ _ _ _ bs (by rw [ha]; omega) (by rw [hb]; omega)
          (by rw [hc]; omega) (by rw [hd]; omega) (by rw [ha, hb, hc, hd, he]; omega)
          (by rw [ha, hb, hc, hd, he]; exact hmax), ha, hb, hc, hd, he, Char.ofNat_toNat]

/-- A byte-count fuel bound suffices for every valid UTF-8 string. -/
theorem utf8_complete (cs : List Char) (fuel : Nat) (hf : (utf8Bytes cs).length ≤ fuel) :
    utf8 fuel (pack (utf8Bytes cs)) (utf8Bytes cs).length = .ok cs 0 0 := by
  induction cs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons c cs ih =>
    have hp : 0 < (String.utf8EncodeChar c).length := by
      rw [String.length_utf8EncodeChar]
      exact c.utf8Size_pos
    simp only [utf8Bytes_cons, List.length_append] at hf
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [utf8Bytes_cons, utf8_char, ih fuel (by omega)]
      rfl

/-- Every successful decode with enough fuel consumes exactly its output encoding. -/
theorem utf8_sound {fuel : Nat} {bs : List UInt8} {cs : List Char} {v n : Nat}
    (hf : bs.length ≤ fuel) (h : utf8 fuel (pack bs) bs.length = .ok cs v n) :
    bs = utf8Bytes cs ∧ v = 0 ∧ n = 0 := by
  induction fuel generalizing bs cs v n with
  | zero =>
    have hn : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst bs
    simp only [utf8, pack_nil, List.length_nil, Res.ok.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp only [utf8, pack_nil, List.length_nil, Res.ok.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    | cons a bs =>
      have finish (pre tail : List UInt8) (c : Char) (hs : a :: bs = pre ++ tail)
          (he : String.utf8EncodeChar c = pre) (hl : tail.length ≤ fuel)
          (hr : (utf8 fuel (pack tail) tail.length).bind
            (fun cs v n => .ok (c :: cs) v n) = .ok cs v n) :
          a :: bs = utf8Bytes cs ∧ v = 0 ∧ n = 0 := by
        obtain ⟨cs', v', n', hrec, hout⟩ := Res.bind_eq_ok.1 hr
        simp only [Res.ok.injEq] at hout
        obtain ⟨rfl, rfl, rfl⟩ := hout
        obtain ⟨hbs, hv, hn⟩ := ih hl hrec
        refine ⟨?_, hv, hn⟩
        rw [utf8Bytes_cons, he, ← hbs]
        exact hs
      by_cases ha1 : a.toNat < 128
      · rw [utf8_one fuel a bs ha1] at h
        exact finish [a] bs _ rfl (encode_one a ha1) (by simp at hf; omega) h
      · have h1 := blt_false.2 (show 128 ≤ a.toNat by omega)
        by_cases ha2 : a.toNat < 194
        · simp only [utf8, List.length_cons, land_pack, h1, blt_true.2 ha2,
            Bool.cond_false, Bool.cond_true] at h
          cases h
        · have h2 := blt_false.2 (show 194 ≤ a.toNat by omega)
          by_cases ha3 : a.toNat < 224
          · simp only [utf8, List.length_cons, land_pack, h1, h2, blt_true.2 ha3,
              Bool.cond_false, Bool.cond_true] at h
            simp only [Bool.cond_eq_ite] at h
            split at h
            · rename_i hg
              simp only [Bool.and_eq_true, ble_true] at hg
              cases bs with
              | nil => simp at hg
              | cons b bs =>
                simp only [shift_pack_8, land_pack, cont_true] at hg
                simp only [Nat.reduceMul, shift_pack_16, List.length_cons,
                  show bs.length + 1 + 1 - 2 = bs.length by omega,
                  shift_pack_8, land_pack] at h
                exact finish [a, b] bs _ rfl (encode_two a b ⟨by omega, ha3⟩ hg.2)
                  (by simp at hf; omega) h
            · cases h
          · have h3 := blt_false.2 (show 224 ≤ a.toNat by omega)
            by_cases ha4 : a.toNat < 240
            · simp only [utf8, List.length_cons, land_pack, h1, h2, h3, blt_true.2 ha4,
                Bool.cond_false, Bool.cond_true] at h
              simp only [Bool.cond_eq_ite] at h
              split at h
              · rename_i hg
                simp only [Bool.and_eq_true, Bool.or_eq_true, ble_true, blt_true] at hg
                obtain ⟨⟨⟨⟨hlen, hb⟩, hc⟩, hmin⟩, hv⟩ := hg
                cases bs with
                | nil => simp at hlen
                | cons b bs =>
                  cases bs with
                  | nil => simp at hlen
                  | cons c bs =>
                    simp only [shift_pack_8, shift_pack_16, land_pack, cont_true] at hb hc hmin hv
                    simp only [Nat.reduceMul, shift_pack_24, List.length_cons,
                      show bs.length + 1 + 1 + 1 - 3 = bs.length by omega,
                      shift_pack_8, shift_pack_16, land_pack] at h
                    exact finish [a, b, c] bs _ rfl
                      (encode_three a b c ⟨by omega, ha4⟩ hb hc hmin hv) (by simp at hf; omega) h
              · cases h
            · have h4 := blt_false.2 (show 240 ≤ a.toNat by omega)
              by_cases ha5 : a.toNat < 245
              · simp only [utf8, List.length_cons, land_pack, h1, h2, h3, h4, blt_true.2 ha5,
                  Bool.cond_false, Bool.cond_true] at h
                simp only [Bool.cond_eq_ite] at h
                split at h
                · rename_i hg
                  simp only [Bool.and_eq_true, ble_true, blt_true] at hg
                  obtain ⟨⟨⟨⟨⟨hlen, hb⟩, hc⟩, hd⟩, hmin⟩, hmax⟩ := hg
                  cases bs with
                  | nil => simp at hlen
                  | cons b bs =>
                    cases bs with
                    | nil => simp at hlen
                    | cons c bs =>
                      cases bs with
                      | nil => simp at hlen
                      | cons d bs =>
                        simp only [shift_pack_8, shift_pack_16, shift_pack_24, land_pack,
                          cont_true] at hb hc hd hmin hmax
                        simp only [Nat.reduceMul, shift_pack_32, List.length_cons,
                          show bs.length + 1 + 1 + 1 + 1 - 4 = bs.length by omega,
                          shift_pack_8, shift_pack_16, shift_pack_24, land_pack] at h
                        exact finish [a, b, c, d] bs _ rfl
                          (encode_four a b c d ⟨by omega, ha5⟩ hb hc hd hmin hmax)
                          (by simp at hf; omega) h
                · cases h
              · simp only [utf8, List.length_cons, land_pack, h1, h2, h3, h4,
                  blt_false.2 (show 245 ≤ a.toNat by omega), Bool.cond_false] at h
                cases h

theorem seq_byte_iff {xs bs : List UInt8} : Seq Byte xs bs ↔ bs = xs := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons ha hs ih => simp only [Byte] at ha; simp [ha, ih]
  · intro he
    subst bs
    induction xs with
    | nil => exact .nil
    | cons a xs ih => exact .cons (show Byte a [a] from rfl) ih

/-- `name` parses exactly the grammar's length-prefixed UTF-8 strings. -/
theorem name_parses : Parses name Name := by
  constructor
  · intro bs s v n h
    simp only [name] at h
    obtain ⟨k, v', n', hk, hs⟩ := Res.bind_eq_ok.1 h
    obtain ⟨pre, body, rfl, hnum, rfl, rfl⟩ := u32_parses.sound hk
    simp only [sub] at hs
    cases hl : Nat.blt body.length k
    · have hle := blt_false.1 hl
      have hlen : (body.take k).length = k := List.length_take_of_le hle
      simp only [hl, Bool.cond_false, land_pack_take hle] at hs
      generalize hr : utf8 k (pack (body.take k)) k = r at hs
      cases r with
      | bad => simp [Res.bind] at hs
      | unsup => simp [Res.bind] at hs
      | ok cs v0 n0 =>
        have hh : utf8 k (pack (body.take k)) (body.take k).length = .ok cs v0 n0 := by
          simpa only [hlen] using hr
        obtain ⟨hbytes, rfl, rfl⟩ := utf8_sound (by omega) hh
        simp only [Res.bind, Res.ok.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        have he : (String.ofList cs).toUTF8.toList = body.take k := by
          rw [utf8Bytes_ofList, ← hbytes]
        refine ⟨pre ++ body.take k, body.drop k, ?_, ?_, shiftRight_pack_drop hle, ?_⟩
        · rw [List.append_assoc, List.take_append_drop]
        · refine ⟨pre, body.take k, ?_, ?_, rfl⟩
          · simpa only [he, hlen] using hnum
          · exact seq_byte_iff.2 he.symm
        · simp [Nat.sub_eq]
    · simp [hl] at hs
  · rintro s _ rest ⟨pre, body, hnum, hseq, rfl⟩
    have he := seq_byte_iff.1 hseq
    subst body
    simp only [name, List.append_assoc]
    rw [u32_parses.complete (s.toUTF8.toList ++ rest) hnum, Res.bind_ok]
    have hl : Nat.blt (s.toUTF8.toList.length + rest.length) s.toUTF8.toList.length = false :=
      blt_false.2 (by omega)
    have hutf := utf8_complete s.toList (utf8Bytes s.toList).length (Nat.le_refl _)
    rw [utf8Bytes_toList] at hutf
    simp only [sub, List.length_append, hl, Bool.cond_false, land_pack_append, hutf,
      Res.bind_ok, String.ofList_toList, shiftRight_pack_append, Nat.sub_eq,
      Nat.add_sub_cancel_left]

end FVA.Wasm.Decode
