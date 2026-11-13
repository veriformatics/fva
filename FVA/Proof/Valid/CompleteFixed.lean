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
    seq C (is ++ js) s = (seq C is s).bind (seq (C.addSets (is.flatMap Instr.sets)) js) := by
  induction is generalizing C s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, seq]
    cases instr C i s with
    | none => rfl
    | some s' =>
      simp only [ih, List.flatMap_cons, Context.addSets_addSets]

theorem heapSrc_complete {k : Nat} {h : HeapType} (hs : h.Src k) : heapSrc k h = true := by
  cases h <;> simp_all [heapSrc, HeapType.Src, Nat.blt_eq]

theorem valSrc_complete {k : Nat} {t : ValType} (hs : t.Src k) : valSrc k t = true := by
  cases t with
  | num _ => rfl
  | ref r => exact heapSrc_complete hs

/-- `pop_ref` on an operand matching `ref null h`: its own heap type is at least as precise. -/
theorem refHeap_complete {a : OpType} {h : Option HeapType} (ha : a.Matches (refOp true h)) :
    ∃ h', refHeap a = some h' ∧ a.Matches (refOp true h') ∧
      (refOp false h').Matches (refOp false h) := by
  cases a with
  | bot =>
    refine ⟨none, rfl, trivial, ?_⟩
    cases h <;> trivial
  | refBot =>
    refine ⟨none, rfl, trivial, ?_⟩
    cases h <;> trivial
  | val t =>
    cases h with
    | none => exact ha.elim
    | some hh =>
      cases t with
      | num _ => exact ha.elim
      | ref r =>
        rcases r with ⟨n, hr⟩
        obtain ⟨_, hhh⟩ := ha
        exact ⟨some hr, rfl, ⟨fun _ => rfl, .inl rfl⟩, ⟨id, hhh⟩⟩

theorem conforms_snoc {s rest : Stack} {a t : OpType} {pre : List OpType}
    (hp : pop s = some (a, rest)) (hr : Conforms rest pre) (ha : a.Matches t) :
    Conforms s (pre ++ [t]) := by
  obtain ⟨actual, hf, hm⟩ := hr
  exact ⟨actual ++ [a], pop_fits hp hf, matches_append hm (.cons ha .nil)⟩

theorem num_of_matches {a : OpType} {n : NumType} (h : a.Matches (.val (.num n))) :
    a = .bot ∨ a = .val (.num n) := by
  cases a with
  | bot => exact .inl rfl
  | refBot => exact h.elim
  | val t =>
    cases t with
    | num m =>
      simp only [OpType.Matches, ValType.Sub] at h
      exact .inr (h ▸ rfl)
    | ref _ => exact h.elim

theorem selectType_complete {a b t : OpType} (ht : t = .bot ∨ ∃ n, t = .val (.num n))
    (ha : a.Matches t) (hb : b.Matches t) :
    ∃ v, selectType a b = some v ∧ v.Matches t := by
  rcases ht with rfl | ⟨n, rfl⟩
  · cases a <;> cases b <;> simp_all [OpType.Matches, selectType]
  · rcases num_of_matches ha with rfl | rfl <;> rcases num_of_matches hb with rfl | rfl
    · exact ⟨.bot, rfl, trivial⟩
    · exact ⟨.val (.num n), rfl, OpType.Matches.refl _⟩
    · exact ⟨.val (.num n), rfl, OpType.Matches.refl _⟩
    · exact ⟨.val (.num n), by simp [selectType], OpType.Matches.refl _⟩

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
