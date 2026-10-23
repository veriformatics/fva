import FVA.Proof.Valid.ValidatorStack

namespace FVA.Wasm.Valid

open FVA.Wasm Check

namespace ValidatorProof

theorem local_eq (runs : List (Nat × ValType)) (x : Nat) :
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

theorem fixed_sound {C : Context} {i : Instr} {st : StackType}
    (h : fixed C i = some st) : InstrT C i st := by
  cases i <;> simp only [fixed, Bool.cond_eq_ite, decide_eq_true_eq] at h
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
  case refNull rt => cases h; exact .refNull
  case refFunc x =>
    split at h
    · cases h
    · split at h <;> simp_all [List.any_eq_true, Nat.beq_eq]
      subst st
      exact .refFunc (by assumption) (by assumption)
  case select ts =>
    split at h
    · cases h; exact .selectT
    · cases h
  case localGet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨t, ht, rfl⟩
    exact .localGet (by simpa [local_eq] using ht)
  case localSet x =>
    rcases Option.map_eq_some_iff.mp h with ⟨t, ht, rfl⟩
    exact .localSet (by simpa [local_eq] using ht)
  case localTee x =>
    rcases Option.map_eq_some_iff.mp h with ⟨t, ht, rfl⟩
    exact .localTee (by simpa [local_eq] using ht)
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
    · split at h <;> simp_all
      subst st
      exact .tableCopy (by assumption) (by assumption) (by assumption)
    · cases h
  case tableInit x y =>
    split at h
    · split at h <;> simp_all
      subst st
      exact .tableInit (by assumption) (by assumption) (by assumption)
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
  case call x =>
    rcases Option.map_eq_some_iff.mp h with ⟨ft, ht, rfl⟩
    exact .call ht
  case callIndirect x y =>
    split at h
    · cases h; exact .callIndirect (by assumption) rfl (by assumption)
    · cases h
  all_goals cases h

end ValidatorProof
end FVA.Wasm.Valid
