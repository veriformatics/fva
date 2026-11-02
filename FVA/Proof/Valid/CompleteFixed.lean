import FVA.Proof.Valid.CompleteStack

namespace FVA.Wasm.Valid

open FVA.Wasm Check ValidatorProof

namespace CompletenessProof

theorem unary_complete {w : Width} {op : IUnOp} (h : IUnOp.Legal w op) :
    unary w op = true := by
  cases w <;> cases op <;> simp_all [unary, IUnOp.Legal]

theorem packed_complete {w : Width} {p : PackSize} (h : PackSize.Legal w p) :
    packed w p = true := by
  cases w <;> cases p <;> simp_all [packed, PackSize.Legal]

theorem memArg_complete {m : MemArg} {n : Nat} (h : m.WF n) (hn : n ≤ 8) :
    memArg m n = true := by
  have ha : m.align ≤ 3 := by
    by_contra hlarge
    have he : 2 ^ 4 ≤ 2 ^ m.align := Nat.pow_le_pow_right (by decide) (by omega)
    have hb := h.1
    norm_num at he
    omega
  simpa [memArg, Nat.ble_eq, Nat.blt_eq] using ⟨⟨ha, h.1⟩, h.2⟩

theorem seq_append (C : Context) (is js : List Instr) (s : Stack) :
    seq C (is ++ js) s = (seq C is s).bind (seq C js) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, seq]
    cases instr C i s <;> simp_all

theorem selectType_complete {a b t : OpType} (ht : t = .bot ∨ ∃ n, t = .val (.num n))
    (ha : a.Matches t) (hb : b.Matches t) :
    ∃ v, selectType a b = some v ∧ v.Matches t := by
  rcases ht with rfl | ⟨n, rfl⟩
  · cases a <;> cases b <;> simp_all [OpType.Matches, selectType]
  · cases a with
    | bot =>
      cases b with
      | bot => exact ⟨.bot, rfl, trivial⟩
      | val u =>
        simp only [OpType.Matches] at hb
        subst u
        exact ⟨.val (.num n), rfl, rfl⟩
    | val u =>
      simp only [OpType.Matches] at ha
      subst u
      cases b with
      | bot => exact ⟨.val (.num n), rfl, rfl⟩
      | val v =>
        simp only [OpType.Matches] at hb
        subst v
        exact ⟨.val (.num n), by simp [selectType], rfl⟩

theorem branch_complete {s : Stack} {pre discard : List OpType} {ts : List ValType}
    (h : Conforms s (pre ++ (discard ++ ops ts))) : branch ts s = some ⟨[], true⟩ := by
  obtain ⟨actual, rest, hp, _, _⟩ := pops_complete
    (pre := pre ++ discard) (abstract := (ops ts).reverse)
    (by simpa [List.append_assoc] using h) (matches_refl _)
  simp [branch, hp]

theorem select_complete {C : Context} {s : Stack} {pre : List OpType} {t : OpType}
    (ht : t = .bot ∨ ∃ n, t = .val (.num n))
    (h : Conforms s (pre ++ [t, t, i32])) :
    ∃ out, instr C (.select none) s = some out ∧ Conforms out (pre ++ [t]) := by
  obtain ⟨selector, r₀, hp₀, _, hr₀⟩ := pops_complete
    (pre := pre ++ [t, t]) (abstract := [i32])
    (by simpa [List.append_assoc] using h) (matches_refl _)
  obtain ⟨a, r₁, hp₁, ha, hr₁⟩ := conforms_pop
    (ts := pre ++ [t]) (by simpa [List.append_assoc] using hr₀)
  obtain ⟨b, r₂, hp₂, hb, hr₂⟩ := conforms_pop hr₁
  obtain ⟨v, hv, hm⟩ := selectType_complete ht ha hb
  exact ⟨push [v] r₂, by simp [instr, hp₀, hp₁, hp₂, hv],
    conforms_push hr₂ (.cons hm .nil)⟩

theorem brTable_complete {C : Context} {s : Stack} {pre t₁ ts t₂ : List OpType}
    {ls : List Nat} {l : Nat}
    (ht : ∀ k ∈ l :: ls, ∃ ts', C.labels[k]? = some ts' ∧ Matches ts (ops ts'))
    (h : Conforms s (pre ++ (t₁ ++ ts ++ [i32]))) :
    ∃ out, instr C (.brTable ls l) s = some out ∧ Conforms out (pre ++ t₂) := by
  obtain ⟨dest, hl, hm⟩ := ht l (by simp)
  obtain ⟨selector, r₀, hp₀, _, hr₀⟩ := pops_complete
    (pre := pre ++ t₁ ++ ts) (abstract := [i32])
    (by simpa [List.append_assoc] using h) (matches_refl _)
  obtain ⟨actual, r₁, hp₁, ha, _⟩ := pops_complete
    (pre := pre ++ t₁) (abstract := ts.reverse) (wanted := (ops dest).reverse)
    (by simpa [List.append_assoc] using hr₀) (matches_reverse hm)
  have htargets : targets C actual ls = true := by
    simp only [targets, List.all_eq_true]
    intro k hk
    obtain ⟨dest', hk', hm'⟩ := ht k (by simp [hk])
    simp only [hk']
    exact matchTypeList_complete (ha.trans (matches_reverse hm'))
  exact ⟨⟨[], true⟩, by simp [instr, hl, hp₀, hp₁, htargets], conforms_reset _⟩

end CompletenessProof
end FVA.Wasm.Valid
