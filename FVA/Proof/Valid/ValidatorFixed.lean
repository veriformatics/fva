import FVA.Proof.Valid.ValidatorStack

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem local_eq (runs : List (Nat × LocalType)) (x : Nat) :
    lookupLocal runs x = localAt runs x := by
  induction runs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [lookupLocal, localAt, Nat.blt_eq, Bool.cond_eq_ite]
    split <;> simp_all

theorem unary_sound {w : Width} {op : IUnOp} (h : unary w op = true) : IUnOp.Legal w op := by
  cases w <;> cases op <;> simp_all [unary, IUnOp.Legal]

theorem packed_sound {w : Width} {p : PackSize} (h : packed w p = true) : PackSize.Legal w p := by
  cases w <;> cases p <;> simp_all [packed, PackSize.Legal]

theorem memArg_sound {m : MemArg} {n : Nat} (h : memArg m n = true) : m.WF n := by
  simp only [memArg, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem blockType_eq (C : Context) (bt : BlockType) : blockType C bt = C.blockType bt := by
  cases bt with
  | val t =>
    simp only [blockType, Context.blockType, Bool.cond_eq_ite]
    by_cases ht : t.Src C.types.length
    · have hb : valSrc C.types.length t = true := by
        cases t with
        | num _ => rfl
        | ref r =>
          rcases r with ⟨n, h⟩
          cases h <;> simp_all [valSrc, heapSrc, ValType.Src, HeapType.Src, Nat.blt_eq]
      simp [hb, ht]
    · have hb : valSrc C.types.length t = false := by
        cases hv : valSrc C.types.length t
        · rfl
        · exact absurd (valSrc_sound hv) ht
      simp [hb, ht]
  | _ => rfl

theorem catchOk_sound {C : Context} {c : Catch} (h : catchOk C c = true) : CatchOK C c := by
  cases c with
  | tag x l =>
    simp only [catchOk] at h
    split at h
    · exact ⟨_, _, by assumption, by assumption, subTypes_sound h⟩
    · cases h
  | tagRef x l =>
    simp only [catchOk] at h
    split at h
    · exact ⟨_, _, by assumption, by assumption, subTypes_sound h⟩
    · cases h
  | all l =>
    simp only [catchOk] at h
    split at h
    · exact by assumption
    · cases h
  | allRef l =>
    simp only [catchOk] at h
    split at h
    · exact ⟨_, by assumption, subTypes_sound h⟩
    · cases h

theorem fixed_sound {C : Context} {i : Instr} {st : StackType}
    (h : fixed C i = some st) : InstrT C i st := by
  cases i <;> simp only [fixed, Bool.cond_eq_ite] at h
  case iconst w n =>
    split at h <;> simp_all [Nat.blt_eq]
    subst st
    exact .iconst (by assumption)
  case fconst w n =>
    split at h <;> simp_all [Nat.blt_eq]
    subst st
    exact .fconst (by assumption)
  case iunop w op =>
    split at h <;> simp_all
    subst st
    exact .iunop (unary_sound (by assumption))
  case ibinop w op => cases h; exact .ibinop
  case itestEqz w => cases h; exact .itestEqz
  case irelop w op => cases h; exact .irelop
  case funop w op => cases h; exact .funop
  case fbinop w op => cases h; exact .fbinop
  case frelop w op => cases h; exact .frelop
  case cvtop op => cases h; exact .cvtop
  case refNull ht =>
    split at h
    · cases h; exact .refNull (heapSrc_sound (by assumption))
    · cases h
  case refFunc x =>
    split at h
    · cases h
    · split at h <;> simp_all [List.any_eq_true, Nat.beq_eq]
      subst st
      exact .refFunc (by assumption) (by assumption)
  case select ts =>
    split at h
    · split at h
      · cases h; exact .selectT (valSrc_sound (by assumption))
      · cases h
    · cases h
  case localGet x =>
    split at h
    · cases h
    · rename_i lt hl
      split at h
      · rename_i hs
        cases h
        simp only [Bool.or_eq_true, List.any_eq_true, Nat.beq_eq] at hs
        refine .localGet (by simpa [local_eq] using hl) ?_
        rcases hs with (hs | hs) | ⟨y, hy, rfl⟩
        · exact .inl hs
        · exact .inr (.inr hs)
        · exact .inr (.inl hy)
      · cases h
  case localSet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨lt, hl, rfl⟩
    exact .localSet (by simpa [local_eq] using hl)
  case localTee x =>
    rcases Option.map_eq_some_iff.mp h with ⟨lt, hl, rfl⟩
    exact .localTee (by simpa [local_eq] using hl)
  case globalGet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨gt, ht, rfl⟩
    exact .globalGet ht
  case globalSet x =>
    split at h
    · cases h; exact .globalSet (by assumption)
    · cases h
  case tableGet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨tt, ht, rfl⟩
    exact .tableGet ht
  case tableSet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨tt, ht, rfl⟩
    exact .tableSet ht
  case tableSize x =>
    rcases Option.map_eq_some_iff.mp h with ⟨tt, ht, rfl⟩
    exact .tableSize ht
  case tableGrow x =>
    rcases Option.map_eq_some_iff.mp h with ⟨tt, ht, rfl⟩
    exact .tableGrow ht
  case tableFill x =>
    rcases Option.map_eq_some_iff.mp h with ⟨tt, ht, rfl⟩
    exact .tableFill ht
  case tableCopy x y =>
    split at h
    · split at h
      · cases h; exact .tableCopy (by assumption) (by assumption) (subType_sound (by assumption))
      · cases h
    · cases h
  case tableInit x y =>
    split at h
    · split at h
      · cases h; exact .tableInit (by assumption) (by assumption) (subType_sound (by assumption))
      · cases h
    · cases h
  case elemDrop x =>
    rcases Option.map_eq_some_iff.mp h with ⟨rt, ht, rfl⟩
    exact .elemDrop ht
  case load t m =>
    split at h
    · cases h
    · split at h <;> simp_all
      subst st
      exact .load (by assumption) (memArg_sound (by aesop))
  case loadPacked w p sx m =>
    split at h
    · cases h
    · split at h <;> simp_all
      subst st
      exact .loadPacked (by assumption) (packed_sound (by aesop))
        (memArg_sound (by aesop))
  case store t m =>
    split at h
    · cases h
    · split at h <;> simp_all
      subst st
      exact .store (by assumption) (memArg_sound (by aesop))
  case storePacked w p m =>
    split at h
    · cases h
    · split at h <;> simp_all
      subst st
      exact .storePacked (by assumption) (packed_sound (by aesop))
        (memArg_sound (by aesop))
  case memorySize =>
    rcases Option.map_eq_some_iff.mp h with ⟨lim, ht, rfl⟩
    exact .memorySize ht
  case memoryGrow =>
    rcases Option.map_eq_some_iff.mp h with ⟨lim, ht, rfl⟩
    exact .memoryGrow ht
  case memoryFill =>
    rcases Option.map_eq_some_iff.mp h with ⟨lim, ht, rfl⟩
    exact .memoryFill ht
  case memoryCopy =>
    rcases Option.map_eq_some_iff.mp h with ⟨lim, ht, rfl⟩
    exact .memoryCopy ht
  case memoryInit x =>
    split at h
    · cases h
    · split at h <;> simp_all [Nat.blt_eq]
      subst st
      exact .memoryInit (by assumption) (by assumption)
  case dataDrop x =>
    split at h <;> simp_all [Nat.blt_eq]
    subst st
    exact .dataDrop (by assumption)
  case nop => cases h; exact .nop
  case brIf l =>
    rcases Option.map_eq_some_iff.mp h with ⟨ts, ht, rfl⟩
    exact .brIf ht
  case brOnNonNull l =>
    split at h
    · rename_i lts hl
      split at h
      · rename_i n hh hlast
        cases h
        have he : lts = lts.dropLast ++ [.ref ⟨n, hh⟩] := by
          rw [← List.dropLast_append_getLast? _ hlast]
          simp
        exact .brOnNonNull (by rw [hl, ← he])
      · cases h
    · cases h
  case call x =>
    rcases Option.map_eq_some_iff.mp h with ⟨ft, ht, rfl⟩
    exact .call ht
  case callIndirect x y =>
    split at h
    · split at h
      · cases h; exact .callIndirect (by assumption) (subType_sound (by assumption)) (by assumption)
      · cases h
    · cases h
  case callRef y =>
    split at h
    · cases h
    · rcases Option.map_eq_some_iff.mp h with ⟨ft, he, rfl⟩
      exact .callRef (by assumption) he
  all_goals cases h

end ValidatorProof
end FVA.Wasm.Valid
