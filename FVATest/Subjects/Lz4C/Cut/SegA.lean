import FVATest.Subjects.Lz4C.Loop
import FVATest.Subjects.Lz4C.ExtDirect
import FVATest.Subjects.Lz4C.Cut.ErrRet

/-! `SegA` (`Seg.lean`) by stepping around checkpoint 1's loop lemma `ExtL1` (`ExtDirect.ext_l1`):
the two bound checks, the first extension byte, the loop for the rest, the length's overflow
guards; `extM` = what `ExtL1`'s exits read (proof support; outside the review surface). -/

namespace Subjects.Lz4C.Cut

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num Subjects.Lz4C

/-- The first bound check (`ip + 1 < iend − 15`). -/
def g1 : List Instr := [.localGet 15, .localGet 14, .irelop .w32 (.lt .u), .brIf 0, .localGet 15,
  .localSet 4, .br 7]

/-- The second bound check (`ip + 2 ≤ iend − 15`, implied by the first). -/
def g2 : List Instr := [.localGet 4, .iconst .w32 2, .ibinop .w32 .add, .localTee 2, .localGet 14,
  .irelop .w32 (.le .u), .brIf 0, .localGet 2, .localSet 4, .br 7]

/-- The first extension byte: done unless it is 255. -/
def b10 : List Instr := [.localGet 15, .loadPacked .w32 .p8 .u ⟨0, 0⟩, .localTee 17,
  .iconst .w32 255, .irelop .w32 .eq, .brIf 0, .localGet 2, .localSet 4, .br 1]

/-- The extension block: the first byte, then the loop from `acc = 255`. -/
noncomputable def ext3 : List Instr :=
  [.block .empty b10, .iconst .w32 255, .localSet 17, extLoop]

/-- After the extension block: `len = acc + 15` and its two overflow guards. -/
def tailA : List Instr := [.localGet 17, .iconst .w32 15, .ibinop .w32 .add, .localTee 2,
  .localGet 3, .iconst .w32 4294967295, .ibinop .w32 .xor, .irelop .w32 (.gt .u), .brIf 6,
  .localGet 2, .localGet 4, .iconst .w32 4294967295, .ibinop .w32 .xor, .irelop .w32 (.gt .u),
  .brIf 6]

theorem body8_drop1 : body8.drop 1 = .block .empty g1 :: .block .empty g2 :: .block .empty ext3 ::
    body8.drop 4 := by kernel_rfl
theorem body8_drop4 : body8.drop 4 = tailA := by kernel_rfl
theorem body2_drop1 :
    body2.drop 1 = [.localGet 2, .iconst .w32 1, .ibinop .w32 .add, .localSet 4] := by kernel_rfl

theorem psum_zero (acc : Nat) (b : Nat → UInt8) : psum acc b 0 = acc + (b 0).toNat := by
  simp [psum]

/-- One period of the sum: the first byte, then the bytes from `p + 1`. -/
theorem psum_shift (acc : Nat) (mem : MemInst) (p i : Nat) :
    psum acc (fun j => mem.byte (p + j)) (i + 1) =
      psum (acc + (mem.byte p).toNat) (fun j => mem.byte (p + 1 + j)) i := by
  unfold psum
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, Nat.add_zero]
  have hf : (fun x => (mem.byte (p + Nat.succ x)).toNat) = fun j => (mem.byte (p + 1 + j)).toNat :=
    funext fun j => by rw [show p + Nat.succ j = p + 1 + j by omega]
  rw [hf]
  omega

theorem psum_first {mem : MemInst} {p acc : Nat} :
    psum acc (fun j => mem.byte (p + j)) 0 = acc + (mem.byte p).toNat := by
  rw [psum_zero, Nat.add_zero]

theorem shift_ff {mem : MemInst} {p k : Nat} (hff : ∀ j < k + 1, mem.byte (p + j) = 255) :
    ∀ j < k, mem.byte (p + 1 + j) = 255 :=
  fun j hj => by rw [show p + 1 + j = p + (j + 1) by omega]; exact hff (j + 1) (by omega)

theorem byte255 {mem : MemInst} {p k : Nat} (hff : ∀ j < k + 1, mem.byte (p + j) = 255) :
    (mem.byte p).toNat = 255 := by
  have := hff 0 (by omega); rw [Nat.add_zero] at this; rw [this]; rfl

/-- `ExtL1`'s normal exit after `k + 1` reads: `extM` returns the sum and the position after. -/
theorem extM_normal {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat), k + 1 ≤ fuel →
    (∀ j < k, mem.byte (p + j) = 255) → mem.byte (p + k) ≠ 255 → p + k + 1 ≤ lim →
    (∀ i ≤ k, psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    extM mem lim fuel p acc = some (psum acc (fun j => mem.byte (p + j)) k, p + k + 1)
  | _, _, _, 0, hf, _, _, _, _ => absurd hf (by omega)
  | 0, p, acc, fuel + 1, _, _, hk, hl, hs => by
    have h0 := hs 0 (Nat.le_refl _)
    rw [psum_first] at h0 ⊢
    rw [Nat.add_zero] at hk
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0]
    rw [ite_eq_right fun h => hk (UInt8.toNat_inj.mp (by rw [h]; rfl))]
  | k + 1, p, acc, fuel + 1, hf, hff, hk, hl, hs => by
    have h0 := hs 0 (Nat.zero_le _)
    rw [psum_first] at h0
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0,
      ite_eq_left (byte255 hff)]
    have ih := extM_normal (lim := lim) k (p + 1) (acc + (mem.byte p).toNat) fuel (by omega)
      (shift_ff hff)
      (by rw [show p + 1 + k = p + (k + 1) by omega]; exact hk) (by omega)
      (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
    rw [ih, psum_shift, show p + 1 + k + 1 = p + (k + 1) + 1 by omega]

/-- `ExtL1`'s bound exit: `extM` fails (at any fuel). -/
theorem extM_bound_exit {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat),
    (∀ j < k, mem.byte (p + j) = 255) → lim < p + k + 1 →
    (∀ i, i + 1 ≤ k → psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    extM mem lim fuel p acc = none
  | _, _, _, 0, _, _, _ => rfl
  | 0, p, acc, fuel + 1, _, hl, _ => by
    simp only [extM, ite_eq_right (show ¬ p + 1 ≤ lim by omega)]
  | k + 1, p, acc, fuel + 1, hff, hl, hs => by
    by_cases hp : p + 1 ≤ lim
    · have h0 := hs 0 (by omega)
      rw [psum_first] at h0
      simp only [extM, ite_eq_left hp, ite_eq_left h0, ite_eq_left (byte255 hff)]
      exact extM_bound_exit k (p + 1) _ fuel (shift_ff hff) (by omega)
        (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
    · simp only [extM, ite_eq_right hp]

/-- `ExtL1`'s overflow exit: `extM` fails (at any fuel). -/
theorem extM_overflow_exit {mem : MemInst} {lim : Nat} : ∀ (k p acc fuel : Nat),
    (∀ j < k, mem.byte (p + j) = 255) → p + k + 1 ≤ lim →
    (∀ i, i + 1 ≤ k → psum acc (fun j => mem.byte (p + j)) i < 2 ^ 31) →
    2 ^ 31 ≤ psum acc (fun j => mem.byte (p + j)) k → extM mem lim fuel p acc = none
  | _, _, _, 0, _, _, _, _ => rfl
  | 0, p, acc, fuel + 1, _, hl, _, ho => by
    rw [psum_first] at ho
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega),
      ite_eq_right (show ¬ acc + (mem.byte p).toNat < 2 ^ 31 by omega)]
  | k + 1, p, acc, fuel + 1, hff, hl, hs, ho => by
    have h0 := hs 0 (by omega)
    rw [psum_first] at h0
    simp only [extM, ite_eq_left (show p + 1 ≤ lim by omega), ite_eq_left h0,
      ite_eq_left (byte255 hff)]
    exact extM_overflow_exit k (p + 1) _ fuel (shift_ff hff) (by omega)
      (fun i hi => by rw [← psum_shift]; exact hs (i + 1) (by omega))
      (by rw [← psum_shift]; exact ho)

end Subjects.Lz4C.Cut
