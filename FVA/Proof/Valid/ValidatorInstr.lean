import FVA.Proof.Valid.ValidatorFlow

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

mutual

theorem instr_typed (i : Instr) {C : Context} {s out : Stack}
    (h : instr C i s = some out) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) : Typed C (es ++ [i]) ins out := by
  cases i with
  | unreachable => cases h; exact reset_typed ht
  | drop =>
    simp only [instr, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, rest⟩, hp, rfl⟩ := h
    have hm : a.Matches a := by cases a <;> simp [OpType.Matches]
    simpa [push] using pop_typed hp hm InstrT.drop ht
  | refIsNull =>
    simp only [instr] at h
    split at h
    · rename_i rest hp
      cases h
      exact pop_typed (wanted := .val (.ref .funcref)) hp trivial .refIsNull ht
    · rename_i rt rest hp
      cases h
      exact pop_typed (wanted := .val (.ref rt)) hp rfl .refIsNull ht
    · cases h
  | select ts =>
    cases ts with
    | none =>
      simp only [instr] at h
      split at h
      · cases h
      · rename_i selector r₀ hp₀
        split at h
        · cases h
        · rename_i a r₁ hp₁
          split at h
          · cases h
          · rename_i b r₂ hp₂
            obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
            exact select_typed hp₀ hp₁ hp₂ hv ht
    | some ts =>
      simp only [instr] at h
      split at h
      · cases h
      · exact apply_typed (fixed_sound (by assumption)) h ht
  | block bt body =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · cases h
    · rename_i ft hb
      split at h
      · cases h
      · rename_i result hs
        split at h
        · rename_i hf
          have typed : SeqT (C.withLabel ft.results) body ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf
            simpa using seq_typed body hs (start_typed _ _)
          exact apply_typed (.block hb typed) h ht
        · cases h
  | loop bt body =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · cases h
    · rename_i ft hb
      split at h
      · cases h
      · rename_i result hs
        split at h
        · rename_i hf
          have typed : SeqT (C.withLabel ft.params) body ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf
            simpa using seq_typed body hs (start_typed _ _)
          exact apply_typed (.loop hb typed) h ht
        · cases h
  | if_ bt thn els =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · cases h
    · rename_i ft hb
      split at h
      · rename_i result₁ result₂ hs₁ hs₂
        split at h
        · rename_i hf
          simp only [Bool.and_eq_true] at hf
          obtain ⟨hf₁, hf₂⟩ := hf
          have typed₁ : SeqT (C.withLabel ft.results) thn ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf₁
            simpa using seq_typed thn hs₁ (start_typed _ _)
          have typed₂ : SeqT (C.withLabel ft.results) els ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf₂
            simpa using seq_typed els hs₂ (start_typed _ _)
          exact apply_typed (.if_ hb typed₁ typed₂) h ht
        · cases h
      · cases h
  | br l =>
    simp only [instr] at h
    split at h
    · cases h
    · exact branch_typed (fun _ _ => .br (by assumption)) h ht
  | return_ =>
    simp only [instr] at h
    split at h
    · cases h
    · exact branch_typed (fun _ _ => .return_ (by assumption)) h ht
  | brTable ls l =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · rename_i ts selector r₀ hl hp₀
      split at h
      · rename_i actual r₁ hp₁
        split at h
        · rename_i htg
          cases h
          exact brTable_typed hl hp₀ hp₁ htg ht
        · cases h
      · cases h
    · cases h
  | _ =>
    simp only [instr] at h
    split at h
    · cases h
    · exact apply_typed (fixed_sound (by assumption)) h ht
termination_by structural i

theorem seq_typed (is : List Instr) {C : Context} {s out : Stack}
    (h : seq C is s = some out) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) : Typed C (es ++ is) ins out := by
  cases is with
  | nil => cases h; simpa using ht
  | cons i is =>
    simp only [seq] at h
    cases hi : instr C i s with
    | none => simp [hi] at h
    | some next =>
      simp only [hi] at h
      have hi' := instr_typed i hi ht
      have hs' := seq_typed is h hi'
      simpa [List.append_assoc] using hs'
termination_by structural is

end

theorem expr_sound {C : Context} {e : Expr} {ts : List ValType} (h : expr C e ts = true) :
    ExprT C e ts := by
  simp only [expr] at h
  cases hs : seq C e {} with
  | none => simp [hs] at h
  | some out =>
    simp only [hs] at h
    refine ⟨ops ts, ?_, matches_refl _⟩
    apply finish_typed h
    simpa using seq_typed e hs (start_typed C [])

end ValidatorProof
end FVA.Wasm.Valid
