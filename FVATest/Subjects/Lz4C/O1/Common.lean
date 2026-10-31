import FVATest.Subjects.Lz4C.O1.Ext
import FVATest.Subjects.Lz4C.ExtCommon

/-! What both routes step the `-O1` loop with: the loop head, `q − 1` arithmetic, the exit-locals
tactic (proof support; outside the review surface). -/

namespace Subjects.Lz4C.O1

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref FVA.Wasm.Num

theorem iadd_minus_one {q : Nat} (h1 : 1 ≤ q) (h : q < 2 ^ 32) :
    iadd (BitVec.ofNat 32 q) (BitVec.ofNat 32 4294967295) = BitVec.ofNat 32 (q - 1) := by
  rw [iadd_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- The `-O1` loop head. -/
noncomputable def head (C : Context) (s : Store) (f : Frame) : Config :=
  (ctx C).fill ⟨s, f, [.label 0 [.loop .empty extBody] (extBody.map .plain)]⟩

/-- `LocalsAt` of an exit frame built by `List.set`s from a head frame: index by
index, the updated locals by computation, the others from the head frame's invariant. -/
macro "locals_at" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro i
  by_cases h₃ : i = 3; · subst h₃; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₄ : i = 4; · subst h₄; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₁₆ : i = 16; · subst h₁₆; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₁₇ : i = 17; · subst h₁₇; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₁₈ : i = 18; · subst h₁₈; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₁₉ : i = 19; · subst h₁₉; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  by_cases h₂₀ : i = 20; · subst h₂₀; simp [List.getElem?_set, List.lookup, beq_iff_eq, $ls,*]
  have e₃ : (i == 3) = false := by simpa using h₃
  have e₄ : (i == 4) = false := by simpa using h₄
  have e₁₆ : (i == 16) = false := by simpa using h₁₆
  have e₁₇ : (i == 17) = false := by simpa using h₁₇
  have e₁₈ : (i == 18) = false := by simpa using h₁₈
  have e₁₉ : (i == 19) = false := by simpa using h₁₉
  have e₂₀ : (i == 20) = false := by simpa using h₂₀
  simp [List.getElem?_set, List.lookup, Ne.symm h₃, Ne.symm h₄, Ne.symm h₁₆, Ne.symm h₁₇,
    Ne.symm h₁₈, Ne.symm h₁₉, Ne.symm h₂₀, h₃, h₄, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, e₃, e₄, e₁₆, e₁₇, e₁₈,
    e₁₉, e₂₀, $ls,*]))

end Subjects.Lz4C.O1
