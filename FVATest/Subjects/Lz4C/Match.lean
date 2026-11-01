import FVATest.Subjects.Lz4C.Loop

/-!
# The match copy ↔ `Lz4.copy` (contract U20, I7)

func 2 copies a match as forward copies whose distance is a multiple of the offset `off`: at
`off ≥ 8` every copy at distance `off`; below 8, four bytes at distance `off`, four at the
`inc32table` distance, the rest at the `dec64table` distance (`off = 0`: zeros). A forward copy
from inside a window whose bytes each repeat the byte `off` before them, at such a distance,
extends the window; that window, from `off` bytes before the match on, holds what `Lz4.copy`
appends (proof support; outside the review surface).
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- From `a + off` up to `w`, each byte of `mem` repeats the byte `off` before it. -/
def Rep (mem : MemInst) (off a w : Nat) : Prop :=
  ∀ x, a + off ≤ x → x < w → mem.byte x = mem.byte (x - off)

theorem Rep.mono {mem : MemInst} {off a w a' w' : Nat} (h : Rep mem off a w) (ha : a ≤ a')
    (hw : w' ≤ w) : Rep mem off a' w' := fun x hx hx' => h x (by omega) (by omega)

theorem Rep.empty (mem : MemInst) (off a : Nat) : Rep mem off a (a + off) :=
  fun _ hx hx' => absurd hx' (by omega)

/-- `j` periods back. -/
theorem Rep.back {mem : MemInst} {off a w : Nat} (h : Rep mem off a w) :
    ∀ (j x : Nat), a + j * off ≤ x → x < w → mem.byte x = mem.byte (x - j * off)
  | 0, x, _, _ => by simp
  | j + 1, x, hx, hw => by
    rw [Nat.succ_mul] at hx ⊢
    rw [Rep.back h j x (by omega) hw, h (x - j * off) (by omega) (by omega)]
    congr 1; omega

/-- Writing at `h ≤ w` the byte `D = (j + 1)·off` back (inside the window) extends the window
to `h + 1`. -/
theorem write1_rep {mem : MemInst} {off a w h j D : Nat} (ho : 0 < off) (hD : D = (j + 1) * off)
    (hr : Rep mem off a w) (ha : a + D ≤ h) (hh : h ≤ w) :
    Rep (mem.write h 1 (mem.byte (h - D)).toNat) off a (max w (h + 1)) := by
  have hjo : (j + 1) * off = j * off + off := Nat.succ_mul j off
  intro x hx hx'
  simp only [write1_byte, UInt8.ofNat_toNat]
  by_cases hxh : x = h
  · subst hxh
    rw [ite_eq_left rfl, ite_eq_right (by omega),
      hr.back j (x - off) (by omega) (by omega)]
    congr 1; omega
  · rw [ite_eq_right hxh]
    by_cases hxo : x - off = h
    · rw [ite_eq_left hxo, hr x (by omega) (by omega), hxo, hD,
        hr.back (j + 1) h (by omega) (by omega)]
    · rw [ite_eq_right hxo]
      exact hr x hx (by omega)

/-- A forward copy at distance `D = (j + 1)·off` from inside the window, written at `h ≤ w`,
extends the window over what it writes. -/
theorem fwdCopy_rep : ∀ (k : Nat) {mem : MemInst} {off a w h j D : Nat}, 0 < off →
    D = (j + 1) * off → Rep mem off a w → a + D ≤ h → h ≤ w →
    Rep (fwdCopy mem h (h - D) k) off a (max w (h + k))
  | 0, mem, off, a, w, h, j, D, _, _, hr, _, hh => by
    rw [show max w (h + 0) = w by omega]; exact hr
  | k + 1, mem, off, a, w, h, j, D, ho, hD, hr, ha, hh => by
    rw [fwdCopy, show h - D + 1 = h + 1 - D by omega]
    have := fwdCopy_rep k (h := h + 1) ho hD (write1_rep ho hD hr ha hh) (by omega)
      (by omega : h + 1 ≤ max w (h + 1))
    rwa [show max (max w (h + 1)) (h + 1 + k) = max w (h + (k + 1)) by omega] at this

/-- The window from `off` bytes before the end of a held prefix holds what `Lz4.copy` appends. -/
theorem holds_copy : ∀ (k : Nat) {mem : MemInst} {dst off : Nat} {out o : List UInt8},
    HoldsAt mem dst out → 0 < off →
    Rep mem off (dst + out.length - off) (dst + out.length + k) →
    Lz4.copy out off k = some o → HoldsAt mem dst o
  | 0, mem, dst, off, out, o, hh, _, _, hc => by
    simp only [Lz4.copy, Option.some.injEq] at hc; subst hc; exact hh
  | k + 1, mem, dst, off, out, o, hh, ho, hr, hc => by
    unfold Lz4.copy at hc
    split at hc
    · rename_i hle
      have hh' : HoldsAt mem dst (out ++ [out[out.length - off]!]) := by
        intro i hi
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hio : i = out.length
        · subst hio
          rw [hr (dst + out.length) (by omega) (by omega),
            show dst + out.length - off = dst + (out.length - off) by omega, hh _ (by omega)]
          simp [List.getElem!_eq_getElem?_getD]
        · rw [hh i (by omega)]
          simp [List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left (show i < out.length by omega)]
      exact holds_copy k hh' ho (hr.mono (by simp; omega) (by simp; omega)) hc
    · simp at hc

/-- From `a` up to `w`, `mem` holds zeros. -/
def Zeros (mem : MemInst) (a w : Nat) : Prop := ∀ x, a ≤ x → x < w → mem.byte x = 0

theorem Zeros.mono {mem : MemInst} {a w a' w' : Nat} (h : Zeros mem a w) (ha : a ≤ a')
    (hw : w' ≤ w) : Zeros mem a' w' := fun x hx hx' => h x (by omega) (by omega)

/-- A forward copy from inside a zero window, written at `h ≤ w`, extends it (a copy onto itself
`s = h` stays inside it). -/
theorem fwdCopy_zeros : ∀ (k : Nat) {mem : MemInst} {a w h s : Nat}, Zeros mem a w → a ≤ s →
    s ≤ h → h ≤ w → (s = h → h + k ≤ w) → Zeros (fwdCopy mem h s k) a (max w (h + k))
  | 0, mem, a, w, h, s, hz, _, _, hh, _ => by
    rw [show max w (h + 0) = w by omega]; exact hz
  | k + 1, mem, a, w, h, s, hz, ha, hs, hh, hself => by
    rw [fwdCopy]
    have hz' : Zeros (mem.write h 1 (mem.byte s).toNat) a (max w (h + 1)) := by
      intro x hx hx'
      rw [write1_byte]
      by_cases hxh : x = h
      · rw [ite_eq_left hxh, hz s ha (by omega)]; rfl
      · rw [ite_eq_right hxh]; exact hz x hx (by omega)
    have := fwdCopy_zeros k (h := h + 1) (s := s + 1) hz' (by omega) (by omega) (by omega)
      (by omega)
    rwa [show max (max w (h + 1)) (h + 1 + k) = max w (h + (k + 1)) by omega] at this

/-- A zero window from the end of a held prefix holds what `Lz4.copy` appends at offset 0. -/
theorem holds_copy_zero : ∀ (k : Nat) {mem : MemInst} {dst : Nat} {out o : List UInt8},
    HoldsAt mem dst out → Zeros mem (dst + out.length) (dst + out.length + k) →
    Lz4.copy out 0 k = some o → HoldsAt mem dst o
  | 0, mem, dst, out, o, hh, _, hc => by
    simp only [Lz4.copy, Option.some.injEq] at hc; subst hc; exact hh
  | k + 1, mem, dst, out, o, hh, hz, hc => by
    unfold Lz4.copy at hc
    rw [ite_eq_left (Nat.zero_le _)] at hc
    have hh' : HoldsAt mem dst (out ++ [out[out.length - 0]!]) := by
      intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hio : i = out.length
      · subst hio
        rw [hz (dst + out.length) (by omega) (by omega)]
        simp; rfl
      · rw [hh i (by omega)]
        simp [List.getElem?_append_left (show i < out.length by omega)]
    exact holds_copy_zero k hh' (hz.mono (by simp) (by simp; omega)) hc

theorem write4_zero (mem : MemInst) (o x : Nat) :
    (mem.write o 4 0).byte x = if o ≤ x ∧ x < o + 4 then 0 else mem.byte x := by
  simp only [MemInst.write, Nat.zero_div]; rfl

theorem toNat_sub_ofNat {x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y).toNat = x - y := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

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

/-- The prologue below offset 8: four single bytes from `o' − off`, four from the `inc32table`
entry, the match pointer moved back by the `dec64table` entry (as `i32`). -/
theorem prologue_small {mem : MemInst} {o' off : Nat} (ht : TablesOK mem) (h7 : off < 8)
    (ho : off ≤ o') (hlt : o' + 8 < 2 ^ 31) :
    (prologue mem o' off).1 = fwdCopy (fwdCopy (mem.write o' 4 0) o' (o' - off) 4) (o' + 4)
      (o' - off + inc32[off]!) 4 ∧
    (prologue mem o' off).2.toNat =
      (o' - off + inc32[off]! + 4294967296 - dec64[off]!) % 4294967296 := by
  obtain ⟨hi, hd⟩ := ht off h7
  have hb : inc32[off]! ≤ 4 ∧ dec64[off]! < 4294967296 := by
    rcases (by omega : off = 0 ∨ off = 1 ∨ off = 2 ∨ off = 3 ∨ off = 4 ∨ off = 5 ∨ off = 6 ∨
      off = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hmp : (BitVec.ofNat 32 o' - BitVec.ofNat 32 off).toNat = o' - off :=
    toNat_sub_ofNat ho (by omega)
  have hp2 : (BitVec.ofNat 32 o' - BitVec.ofNat 32 off + BitVec.ofNat 32 inc32[off]!).toNat =
      o' - off + inc32[off]! := by
    rw [toNat_add_ofNat (by omega), hmp]
  unfold prologue
  rw [ite_eq_right (by omega : ¬ 7 < off)]
  simp only [hi, hd]
  refine ⟨by rw [hmp, hp2], ?_⟩
  rw [BitVec.toNat_sub, hp2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.2]
  omega

/-- The prologue chain from `off ≥ 1`: four bytes at distance `off`, four at `(j + 1)·off`. -/
theorem prologue_chain {mem : MemInst} {o' off j : Nat} (ho : 0 < off) (hoo : off ≤ o')
    (h1 : (j + 1) * off ≤ off + 4) :
    Rep (fwdCopy (fwdCopy (mem.write o' 4 0) o' (o' - off) 4) (o' + 4)
      (o' + 4 - (j + 1) * off) 4) off (o' - off) (o' + 8) := by
  have hr0 := Rep.empty (mem.write o' 4 0) off (o' - off)
  rw [show o' - off + off = o' by omega] at hr0
  have hr1 := fwdCopy_rep 4 (h := o') (j := 0) (D := off) ho (by simp) hr0 (by omega)
    (Nat.le_refl _)
  rw [show max o' (o' + 4) = o' + 4 by omega] at hr1
  have hr2 := fwdCopy_rep 4 (h := o' + 4) (j := j) ho rfl hr1 (by omega) (Nat.le_refl _)
  rwa [show max (o' + 4) (o' + 4 + 4) = o' + 8 by omega] at hr2

/-- After the prologue from `off ≥ 1`, the window from `o' − off` repeats up to `o' + 8`, and the
match pointer lies `(j + 1)·off ≤ off + 8` before `o' + 8`. -/
theorem prologue_rep {mem : MemInst} {o' off : Nat} (ht : TablesOK mem) (ho : 0 < off)
    (hoo : off ≤ o') (hoff : off < 65536) (hlt : o' + 8 < 2 ^ 31) :
    ∃ j D, D = (j + 1) * off ∧ D ≤ off + 8 ∧
      Rep (prologue mem o' off).1 off (o' - off) (o' + 8) ∧
      (prologue mem o' off).2.toNat = o' + 8 - D := by
  by_cases h8 : 7 < off
  · have hmp : (BitVec.ofNat 32 o' - BitVec.ofNat 32 off).toNat = o' - off :=
      toNat_sub_ofNat hoo (by omega)
    have hr0 := Rep.empty mem off (o' - off)
    rw [show o' - off + off = o' by omega] at hr0
    have hr := fwdCopy_rep 8 (h := o') (j := 0) (D := off) ho (by simp) hr0 (by omega)
      (Nat.le_refl _)
    rw [show max o' (o' + 8) = o' + 8 by omega] at hr
    refine ⟨0, off, by simp, by omega, ?_, ?_⟩
    · unfold prologue; rw [ite_eq_left h8, hmp]; exact hr
    · unfold prologue
      rw [ite_eq_left h8]
      have : (BitVec.ofNat 32 o' - BitVec.ofNat 32 off + 8).toNat = o' - off + 8 := by
        have := toNat_add_ofNat (x := BitVec.ofNat 32 o' - BitVec.ofNat 32 off) (y := 8)
          (by omega)
        rwa [hmp] at this
      rw [this]; omega
  · obtain ⟨he, hp⟩ := prologue_small ht (by omega) hoo hlt
    rw [he, hp]
    -- per offset: the inc32 + dec64 entries → distances D1 = (j1 + 1)·off, D = (j + 1)·off
    rcases (by omega : off = 1 ∨ off = 2 ∨ off = 3 ∨ off = 4 ∨ off = 5 ∨ off = 6 ∨ off = 7)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨7, 8, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[1]! = 1 from rfl,
          show o' - 1 + 1 = o' + 4 - (3 + 1) * 1 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[1]! = 1 from rfl, show dec64[1]! = 0 from rfl,
          mod_pos (by omega) (by omega)]
        omega
    · refine ⟨3, 8, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[2]! = 2 from rfl,
          show o' - 2 + 2 = o' + 4 - (1 + 1) * 2 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[2]! = 2 from rfl, show dec64[2]! = 0 from rfl,
          mod_pos (by omega) (by omega)]
        omega
    · refine ⟨2, 9, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[3]! = 1 from rfl,
          show o' - 3 + 1 = o' + 4 - (1 + 1) * 3 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[3]! = 1 from rfl, show dec64[3]! = 4294967296 - 1 from rfl,
          mod_neg (by omega)]
        omega
    · refine ⟨1, 8, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[4]! = 0 from rfl,
          show o' - 4 + 0 = o' + 4 - (1 + 1) * 4 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[4]! = 0 from rfl, show dec64[4]! = 4294967296 - 4 from rfl,
          mod_neg (by omega)]
        omega
    · refine ⟨1, 10, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[5]! = 4 from rfl,
          show o' - 5 + 4 = o' + 4 - (0 + 1) * 5 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[5]! = 4 from rfl, show dec64[5]! = 1 from rfl,
          mod_pos (by omega) (by omega)]
        omega
    · refine ⟨1, 12, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[6]! = 4 from rfl,
          show o' - 6 + 4 = o' + 4 - (0 + 1) * 6 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[6]! = 4 from rfl, show dec64[6]! = 2 from rfl,
          mod_pos (by omega) (by omega)]
        omega
    · refine ⟨1, 14, rfl, by omega, ?_, ?_⟩
      · rw [show inc32[7]! = 4 from rfl,
          show o' - 7 + 4 = o' + 4 - (0 + 1) * 7 by omega]
        exact prologue_chain ho hoo (by omega)
      · rw [show inc32[7]! = 4 from rfl, show dec64[7]! = 3 from rfl,
          mod_pos (by omega) (by omega)]
        omega

/-- After the prologue at offset 0, `[o', o' + 8)` holds zeros and the match pointer is `o'`. -/
theorem prologue_zeros {mem : MemInst} {o' : Nat} (ht : TablesOK mem) (hlt : o' + 8 < 2 ^ 31) :
    Zeros (prologue mem o' 0).1 o' (o' + 8) ∧ (prologue mem o' 0).2.toNat = o' := by
  obtain ⟨he, hp⟩ := prologue_small ht (by omega) (Nat.zero_le o') hlt
  rw [he, hp]
  have hz0 : Zeros (mem.write o' 4 0) o' (o' + 4) := by
    intro x hx hx'; rw [write4_zero, ite_eq_left ⟨hx, hx'⟩]
  have hz1 := fwdCopy_zeros 4 (h := o') (s := o') hz0 (Nat.le_refl _) (Nat.le_refl _) (by omega)
    fun _ => Nat.le_refl _
  rw [show max (o' + 4) (o' + 4) = o' + 4 by omega] at hz1
  have hz2 := fwdCopy_zeros 4 (h := o' + 4) (s := o') hz1 (Nat.le_refl _) (by omega)
    (Nat.le_refl _) (by omega)
  rw [show max (o' + 4) (o' + 4 + 4) = o' + 8 by omega] at hz2
  refine ⟨by rw [Nat.sub_zero, show inc32[0]! = 0 from rfl, Nat.add_zero]; exact hz2, ?_⟩
  rw [show inc32[0]! = 0 from rfl, show dec64[0]! = 0 from rfl, mod_pos (by omega) (by omega)]
  omega

/-- `matchRest` from a pointer `D = (j + 1)·off` before `o' + 8` (inside the window): every copy
keeps that distance, so the window repeats up to the match's end. -/
theorem matchRest_rep {mem : MemInst} {o' m oend off j D : Nat} {mp : BitVec 32} (ho : 0 < off)
    (hD : D = (j + 1) * off) (hr : Rep mem off (o' - off) (o' + 8))
    (hmp : mp.toNat = o' + 8 - D) (hDle : D ≤ off + 8) (hoo : off ≤ o')
    (hroom : o' + m + 4 + 5 ≤ oend) (hlim : oend < 2 ^ 31) :
    Rep (matchRest mem o' m oend mp) off (o' - off) (o' + m + 4) := by
  have hsrc : o' - off + D ≤ o' + 8 := by omega
  have h4 := fwdCopy_rep 8 (h := o' + 8) ho hD hr hsrc (Nat.le_refl _)
  rw [show max (o' + 8) (o' + 8 + 8) = o' + 16 by omega, ← hmp] at h4
  simp only [matchRest]
  split
  · split
    · exact h4.mono (Nat.le_refl _) (by omega)
    · have h8 : (mp + 8).toNat = o' + 16 - D :=
        (toNat_add_ofNat (x := mp) (y := 8) (by omega)).trans (by rw [hmp]; omega)
      rw [h8]
      have := fwdCopy_rep (8 * chunks (o' + 16) (o' + m + 4)) (h := o' + 16) ho hD h4 (by omega)
        (Nat.le_refl _)
      exact this.mono (Nat.le_refl _) (by simp only [chunks]; omega)
  · by_cases hl : o' + 8 < oend - 7
    · simp only [hl, ite_true]
      have hw := fwdCopy_rep (8 * chunks (o' + 8) (oend - 7)) (h := o' + 8) ho hD hr hsrc
        (Nat.le_refl _)
      rw [← hmp] at hw
      have hp : (mp + BitVec.ofNat 32 (oend - 7 - (o' + 8))).toNat = oend - 7 - D := by
        rw [toNat_add_ofNat (by omega), hmp]; omega
      rw [hp]
      split
      · have := fwdCopy_rep (o' + m + 4 - (oend - 7)) (h := oend - 7) ho hD hw (by omega)
          (by simp only [chunks]; omega)
        exact this.mono (Nat.le_refl _) (by omega)
      · exact hw.mono (Nat.le_refl _) (by simp only [chunks]; omega)
    · simp only [hl, ite_false]
      split
      · have := fwdCopy_rep (o' + m + 4 - (o' + 8)) (h := o' + 8) ho hD hr hsrc (Nat.le_refl _)
        rw [← hmp] at this
        exact this.mono (Nat.le_refl _) (by omega)
      · exact hr.mono (Nat.le_refl _) (by omega)

/-- `matchRest` from the pointer `o'` over a zero window `[o', o' + 8)`: zeros up to the match's
end. -/
theorem matchRest_zeros {mem : MemInst} {o' m oend : Nat} {mp : BitVec 32}
    (hz : Zeros mem o' (o' + 8)) (hmp : mp.toNat = o') (hroom : o' + m + 4 + 5 ≤ oend)
    (hlim : oend < 2 ^ 31) : Zeros (matchRest mem o' m oend mp) o' (o' + m + 4) := by
  have h4 := fwdCopy_zeros 8 (h := o' + 8) (s := o') hz (Nat.le_refl _) (by omega)
    (Nat.le_refl _) (by omega)
  rw [show max (o' + 8) (o' + 8 + 8) = o' + 16 by omega] at h4
  have h8 : (mp + 8).toNat = o' + 8 :=
    (toNat_add_ofNat (x := mp) (y := 8) (by omega)).trans (by rw [hmp])
  simp only [matchRest, h8, hmp]
  split
  · split
    · exact h4.mono (Nat.le_refl _) (by omega)
    · have := fwdCopy_zeros (8 * chunks (o' + 16) (o' + m + 4)) (h := o' + 16) (s := o' + 8) h4
        (by omega) (by omega) (Nat.le_refl _) (by omega)
      exact this.mono (Nat.le_refl _) (by simp only [chunks]; omega)
  · by_cases hl : o' + 8 < oend - 7
    · have hp : (mp + BitVec.ofNat 32 (oend - 7 - (o' + 8))).toNat = oend - 7 - 8 := by
        rw [toNat_add_ofNat (by omega), hmp]; omega
      simp only [hl, ite_true, hp]
      have hw := fwdCopy_zeros (8 * chunks (o' + 8) (oend - 7)) (h := o' + 8) (s := o') hz
        (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega)
      split
      · have := fwdCopy_zeros (o' + m + 4 - (oend - 7)) (h := oend - 7) (s := oend - 7 - 8) hw
          (by omega) (by omega) (by simp only [chunks]; omega) (by omega)
        exact this.mono (Nat.le_refl _) (by omega)
      · exact hw.mono (Nat.le_refl _) (by simp only [chunks]; omega)
    · simp only [hl, ite_false]
      split
      · have := fwdCopy_zeros (o' + m + 4 - (o' + 8)) (h := o' + 8) (s := o') hz (Nat.le_refl _)
          (by omega) (Nat.le_refl _) (by omega)
        exact this.mono (Nat.le_refl _) (by omega)
      · exact hz.mono (Nat.le_refl _) (by omega)

/-- SegD's copy of a match of length `m + 4` at `o'` from offset `off` (prologue + rest), with
the decoded prefix `out` held up to `o'`: the destination holds `Lz4.copy out off (m + 4)`. -/
theorem match_holds {mem : MemInst} {dst cap o' off m : Nat} {out o : List UInt8}
    (hh : HoldsAt mem dst out) (ho : o' = dst + out.length) (hoff : off ≤ out.length)
    (hoff' : off < 65536) (hroom : o' + m + 4 + 5 ≤ dst + cap) (hlim : dst + cap < 2 ^ 31)
    (ht : TablesOK mem) (hc : Lz4.copy out off (m + 4) = some o) :
    HoldsAt (matchRest (prologue mem o' off).1 o' m (dst + cap) (prologue mem o' off).2) dst o := by
  have hpre : HoldsAt (matchRest (prologue mem o' off).1 o' m (dst + cap)
      (prologue mem o' off).2) dst out :=
    hh.of_outside fun a _ hb => by
      rw [matchRest_low _ _ _ _ _ _ (by omega), prologue_low _ _ _ _ (by omega)]
  by_cases h0 : off = 0
  · subst h0
    obtain ⟨hz, hp⟩ := prologue_zeros (o' := o') ht (by omega)
    refine holds_copy_zero (m + 4) hpre ?_ hc
    rw [← ho]
    exact matchRest_zeros hz hp hroom hlim
  · obtain ⟨j, D, hD, hDle, hr, hp⟩ := prologue_rep (o' := o') ht (by omega) (by omega) hoff'
      (by omega)
    refine holds_copy (m + 4) hpre (by omega) ?_ hc
    rw [← ho]
    exact matchRest_rep (by omega) hD hr hp hDle (by omega) hroom hlim

end Subjects.Lz4C
