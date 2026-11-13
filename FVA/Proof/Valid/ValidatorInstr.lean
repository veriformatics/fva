import FVA.Proof.Valid.ValidatorFlow

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem ops_append (ts us : List ValType) : ops (ts ++ us) = ops ts ++ ops us := by
  simp only [ops, List.map_append]

mutual

/-- Each instruction the validator accepts extends the declarative derivation; the validator's
context `Cv` reads no more initialized locals than the declarative one (`Next C es`). -/
theorem instr_typed (i : Instr) {Cv C : Context} {s out : Stack}
    (h : instr Cv i s = some out) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) (hc : Cv.Entails (Next C es)) : Typed C (es ++ [i]) ins out := by
  cases i with
  | unreachable => cases h; exact reset_typed ht
  | drop =>
    simp only [instr, Option.map_eq_some_iff] at h
    obtain ⟨⟨a, rest⟩, hp, rfl⟩ := h
    simpa [push] using pop_typed hp a.matches_refl InstrT.drop ht
  | refIsNull =>
    simp only [instr] at h
    split at h
    · cases h
      exact pop_typed (a := .bot) (wanted := .val (.ref .funcref)) (by assumption) trivial
        .refIsNull ht
    · cases h
      exact pop_typed (a := .refBot) (wanted := .val (.ref .funcref)) (by assumption) trivial
        .refIsNull ht
    · rename_i rt _ _
      cases h
      exact pop_typed (a := .val (.ref rt)) (wanted := .val (.ref rt)) (by assumption)
        (OpType.matches_refl _) .refIsNull ht
    · cases h
  | refAsNonNull =>
    simp only [instr] at h
    split at h
    · split at h
      · exact apply_typed InstrT.refAsNonNull h ht
      · cases h
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
      · exact apply_typed ((fixed_sound (by assumption)).transport hc) h ht
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
          have typed : SeqT (Cv.withLabel ft.results) body ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf
            simpa using seq_typed body hs (start_typed _ _) (Context.Entails.addSets_nil _)
          have hb' : Cv.blockType bt = some ft := by rwa [← blockType_eq]
          exact apply_typed ((InstrT.block hb' typed).transport hc) h ht
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
          have typed : SeqT (Cv.withLabel ft.params) body ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf
            simpa using seq_typed body hs (start_typed _ _) (Context.Entails.addSets_nil _)
          have hb' : Cv.blockType bt = some ft := by rwa [← blockType_eq]
          exact apply_typed ((InstrT.loop hb' typed).transport hc) h ht
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
          have typed₁ : SeqT (Cv.withLabel ft.results) thn ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf₁
            simpa using seq_typed thn hs₁ (start_typed _ _) (Context.Entails.addSets_nil _)
          have typed₂ : SeqT (Cv.withLabel ft.results) els ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf₂
            simpa using seq_typed els hs₂ (start_typed _ _) (Context.Entails.addSets_nil _)
          have hb' : Cv.blockType bt = some ft := by rwa [← blockType_eq]
          exact apply_typed ((InstrT.if_ hb' typed₁ typed₂).transport hc) h ht
        · cases h
      · cases h
  | tryTable bt cs body =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · cases h
    · rename_i ft hb
      split at h
      · cases h
      · rename_i result hs
        split at h
        · rename_i hf
          simp only [Bool.and_eq_true, List.all_eq_true] at hf
          obtain ⟨hf, hcs⟩ := hf
          have typed : SeqT (Cv.withLabel ft.results) body ⟨ops ft.params, ops ft.results⟩ := by
            apply finish_typed hf
            simpa using seq_typed body hs (start_typed _ _) (Context.Entails.addSets_nil _)
          have hb' : Cv.blockType bt = some ft := by rwa [← blockType_eq]
          exact apply_typed ((InstrT.tryTable hb' typed
            fun c hc' => catchOk_sound (hcs c hc')).transport hc) h ht
        · cases h
  | br l =>
    simp only [instr] at h
    split at h
    · cases h
    · exact branch_typed (fun _ _ => (InstrT.br (by assumption)).transport hc) h ht
  | return_ =>
    simp only [instr] at h
    split at h
    · cases h
    · exact branch_typed (fun _ _ => (InstrT.return_ (by assumption)).transport hc) h ht
  | brTable ls l =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · rename_i ts selector r₀ hl hp₀
      split at h
      · rename_i actual r₁ hp₁
        split at h
        · rename_i htg
          cases h
          exact brTable_typed hc hl hp₀ hp₁ htg ht
        · cases h
      · cases h
    · cases h
  | brOnNull l =>
    simp only [instr] at h
    split at h
    · rename_i ts a _ hl _
      split at h
      · exact apply_typed ((InstrT.brOnNull hl).transport hc) h ht
      · cases h
    · cases h
  | returnCall x =>
    simp only [instr] at h
    split at h
    · cases h
    · rename_i ft hf
      exact tailCall_typed (fun _ hr hs _ _ => (InstrT.returnCall hf hr hs).transport hc) h ht
  | returnCallIndirect x y =>
    simp only [instr, Bool.cond_eq_ite] at h
    split at h
    · rename_i tt ft htt hy
      split at h
      · rename_i he
        refine tailCall_typed (fun _ hr hs pre _ => ?_) h ht
        rw [ops_append, ← List.append_assoc]
        exact (InstrT.returnCallIndirect htt (subType_sound he) hy hr hs).transport hc
      · cases h
    · cases h
  | returnCallRef y =>
    simp only [instr] at h
    split at h
    · cases h
    · rename_i dt hy
      split at h
      · cases h
      · rename_i ft he
        refine tailCall_typed (fun _ hr hs pre _ => ?_) h ht
        rw [ops_append, ← List.append_assoc]
        exact (InstrT.returnCallRef hy he hr hs).transport hc
  | throw x =>
    simp only [instr] at h
    split at h
    · exact branch_typed (fun _ _ => (InstrT.throw (by assumption)).transport hc) h ht
    · cases h
  | throwRef =>
    simp only [instr] at h
    exact branch_typed (fun _ _ => InstrT.throwRef) h ht
  | _ =>
    simp only [instr] at h
    split at h
    · cases h
    · exact apply_typed ((fixed_sound (by assumption)).transport hc) h ht
termination_by structural i

theorem seq_typed (is : List Instr) {Cv C : Context} {s out : Stack}
    (h : seq Cv is s = some out) {es : List Instr} {ins : List OpType}
    (ht : Typed C es ins s) (hc : Cv.Entails (Next C es)) : Typed C (es ++ is) ins out := by
  cases is with
  | nil => cases h; simpa using ht
  | cons i is =>
    simp only [seq] at h
    cases hi : instr Cv i s with
    | none => simp [hi] at h
    | some next =>
      simp only [hi] at h
      have hi' := instr_typed i hi ht hc
      have hc' : (Cv.addSets i.sets).Entails (Next C (es ++ [i])) := by
        have := hc.addSets i.sets
        simpa only [Next, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, Context.addSets_addSets] using this
      have hs' := seq_typed is h hi' hc'
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
    simpa using seq_typed e hs (start_typed C []) (Context.Entails.addSets_nil C)

end ValidatorProof
end FVA.Wasm.Valid
