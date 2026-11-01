import FVATest.Subjects.Lz4C.Copy
import FVATest.Subjects.Lz4C.ModelProof

/-!
# The decoder's memory ↔ the decoded prefix (contract U20, I7 slice)

The compiled copies are `fwdCopy`s; the format's matches are `Lz4.copy`s. A forward copy from
`off ≥ 1` bytes back is exactly `Lz4.copy` on the bytes the destination already holds, whatever
the overlap, and every byte a copy writes past the decoded prefix stays outside it. So the
shortcut's two copies (16 literal bytes from the input, 18 match bytes) leave the destination
holding the prefix extended by one sequence (proof support; outside the review surface).
-/

namespace Subjects.Lz4C

open FVA.Wasm FVA.Wasm.Exec

/-- Memory `mem` holds `bs` at `p`. -/
def HoldsAt (mem : MemInst) (p : Nat) (bs : List UInt8) : Prop :=
  ∀ i < bs.length, mem.byte (p + i) = bs[i]!

theorem write1_byte (mem : MemInst) (d v a : Nat) :
    (mem.write d 1 v).byte a = if a = d then UInt8.ofNat v else mem.byte a := by
  simp only [MemInst.write]
  by_cases h : a = d
  · subst h; simp
  · rw [ite_eq_right (by omega), ite_eq_right h]

@[simp] theorem fwdCopy_pages : ∀ (n : Nat) (mem : MemInst) (d s : Nat),
    (fwdCopy mem d s n).pages = mem.pages
  | 0, _, _, _ => rfl
  | n + 1, mem, d, s => by rw [fwdCopy, fwdCopy_pages n]; rfl

@[simp] theorem fwdCopy_max : ∀ (n : Nat) (mem : MemInst) (d s : Nat),
    (fwdCopy mem d s n).max = mem.max
  | 0, _, _, _ => rfl
  | n + 1, mem, d, s => by rw [fwdCopy, fwdCopy_max n]; rfl

@[simp] theorem fwdCopy_size (n : Nat) (mem : MemInst) (d s : Nat) :
    (fwdCopy mem d s n).size = mem.size := by
  simp [MemInst.size]

/-- A forward copy writes only `[d, d + n)`. -/
theorem fwdCopy_outside : ∀ (n : Nat) (mem : MemInst) (d s a : Nat), (a < d ∨ d + n ≤ a) →
    (fwdCopy mem d s n).byte a = mem.byte a
  | 0, _, _, _, _, _ => rfl
  | n + 1, mem, d, s, a, h => by
    rw [fwdCopy, fwdCopy_outside n _ _ _ _ (by omega), write1_byte, ite_eq_right (by omega)]

/-- Copying `a + b` bytes = `a` bytes, then `b` more after them. -/
theorem fwdCopy_add : ∀ (a b : Nat) (mem : MemInst) (d s : Nat),
    fwdCopy mem d s (a + b) = fwdCopy (fwdCopy mem d s a) (d + a) (s + a) b
  | 0, b, mem, d, s => by simp [fwdCopy]
  | a + 1, b, mem, d, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega, fwdCopy, fwdCopy_add a b, fwdCopy,
      show d + 1 + a = d + (a + 1) by omega, show s + 1 + a = s + (a + 1) by omega]

/-- With the source ahead of the destination or entirely before it, a forward copy moves the
source bytes as they were. -/
theorem fwdCopy_byte : ∀ (n : Nat) (mem : MemInst) (d s : Nat), (d ≤ s ∨ s + n ≤ d) →
    ∀ i < n, (fwdCopy mem d s n).byte (d + i) = mem.byte (s + i)
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, mem, d, s, h, i, hi => by
    rw [fwdCopy]
    rcases i with _ | i
    · rw [fwdCopy_outside n _ _ _ _ (by omega), write1_byte, ite_eq_left (by omega)]; simp
    · rw [show d + (i + 1) = d + 1 + i by omega,
        fwdCopy_byte n _ (d + 1) (s + 1) (by omega) i (by omega), write1_byte,
        ite_eq_right (by omega)]
      congr 1; omega

/-- A forward copy from `off ≥ 1` bytes behind the end of a held prefix appends `Lz4.copy`'s
bytes: an overlapping match repeats bytes it has just written, as the format does. -/
theorem fwdCopy_lz77 : ∀ (len : Nat) {mem : MemInst} {dst op off : Nat} {out o : List UInt8},
    HoldsAt mem dst out → op = dst + out.length → 1 ≤ off → Lz4.copy out off len = some o →
    HoldsAt (fwdCopy mem op (op - off) len) dst o
  | 0, mem, dst, op, off, out, o, hh, _, _, hc => by
    simp only [Lz4.copy, Option.some.injEq] at hc; subst hc; exact hh
  | len + 1, mem, dst, op, off, out, o, hh, hop, hoff, hc => by
    unfold Lz4.copy at hc
    split at hc
    · rename_i hle
      have hlt : out.length - off < out.length := by omega
      have hh' : HoldsAt (mem.write op 1 (mem.byte (op - off)).toNat) dst
          (out ++ [out[out.length - off]!]) := by
        intro i hi
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        rw [write1_byte]
        by_cases hio : i = out.length
        · subst hio
          rw [ite_eq_left (by omega), show op - off = dst + (out.length - off) by omega,
            hh _ hlt]
          simp [List.getElem!_eq_getElem?_getD]
        · rw [ite_eq_right (by omega), hh i (by omega)]
          simp [List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left (show i < out.length by omega)]
      have h := fwdCopy_lz77 len (op := op + 1) hh' (by simp; omega) hoff hc
      rw [fwdCopy]
      rwa [show op + 1 - off = op - off + 1 by omega] at h
    · simp at hc

theorem HoldsAt.of_outside {mem mem' : MemInst} {p : Nat} {bs : List UInt8} (h : HoldsAt mem p bs)
    (he : ∀ a, p ≤ a → a < p + bs.length → mem'.byte a = mem.byte a) : HoldsAt mem' p bs :=
  fun i hi => (he _ (by omega) (by omega)).trans (h i hi)

/-- The shortcut's two copies extend a held prefix by one sequence: 16 bytes from the input (the
first `ll` = the literals) at `op`, then 18 bytes from `off ≥ 1` back at `op + ll` (the first
`ml + 4` = the match); the input lies wholly after `op` or before the output. -/
theorem shortcut_holds {mem : MemInst} {dst op ip off ml : Nat} {out lits o : List UInt8}
    (hh : HoldsAt mem dst out) (hop : op = dst + out.length) (hsrc : op ≤ ip + 1 ∨ ip + 17 ≤ dst)
    (hlits : HoldsAt mem (ip + 1) lits) (hll : lits.length ≤ 14) (hml : ml ≤ 14)
    (hoff : 1 ≤ off) (hc : Lz4.copy (out ++ lits) off (ml + 4) = some o) :
    HoldsAt (fwdCopy (fwdCopy mem op (ip + 1) 16) (op + lits.length)
      (op + lits.length - off) 18) dst o := by
  have h1 : HoldsAt (fwdCopy mem op (ip + 1) 16) dst (out ++ lits) := by
    intro i hi
    simp only [List.length_append] at hi
    by_cases hio : i < out.length
    · rw [fwdCopy_outside _ _ _ _ _ (by omega), hh i hio]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hio]
    · obtain ⟨j, rfl⟩ : ∃ j, i = out.length + j := ⟨i - out.length, by omega⟩
      rw [show dst + (out.length + j) = op + j by omega,
        fwdCopy_byte _ _ _ _ (by omega) j (by omega), hlits j (by omega)]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right]
  have hol := Model.copy_length hc
  simp only [List.length_append] at hol
  rw [show 18 = (ml + 4) + (14 - ml) by omega, fwdCopy_add]
  refine HoldsAt.of_outside (fwdCopy_lz77 (ml + 4) (op := op + lits.length) h1 (by simp; omega)
    hoff hc) fun a ha hb => ?_
  exact fwdCopy_outside _ _ _ _ _ (by omega)

end Subjects.Lz4C
