import FVA.Spec.Valid.Soundness

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

namespace OpType.Matches

theorem refl (t : OpType) : t.Matches t := by cases t <;> simp [OpType.Matches]

theorem trans {a b c : OpType} (h₁ : a.Matches b) (h₂ : b.Matches c) : a.Matches c := by
  cases a <;> cases b <;> cases c <;> simp_all [OpType.Matches]

theorem of_val {t : ValType} {u : OpType} (h : (.val t : OpType).Matches u) : u = .val t := by
  cases u <;> simp_all [OpType.Matches]

end OpType.Matches

namespace Matches

theorem refl (ts : List OpType) : Matches ts ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (OpType.Matches.refl t) ih

theorem trans {a b c : List OpType} (h₁ : Matches a b) (h₂ : Matches b c) : Matches a c := by
  induction h₁ generalizing c with
  | nil => exact h₂
  | cons h hs ih =>
    cases h₂ with
    | cons h' hs' => exact .cons (OpType.Matches.trans h h') (ih hs')

theorem append {a b c d : List OpType} (h₁ : Matches a b) (h₂ : Matches c d) :
    Matches (a ++ c) (b ++ d) := List.rel_append h₁ h₂

theorem length_eq {a b : List OpType} (h : Matches a b) : a.length = b.length :=
  List.Forall₂.length_eq h

theorem of_ops {ts : List ValType} {us : List OpType} (h : Matches (ops ts) us) :
    us = ops ts := by
  induction ts generalizing us with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases h with
    | cons ht hs => simp only [ops, List.map_cons, OpType.Matches.of_val ht, ih hs]

end Matches

namespace SeqT

private theorem nil_inv {C : Context} {es : List Instr} {st : StackType}
    (h : SeqT C es st) : es = [] → Matches st.ins st.outs := by
  induction h using SeqT.rec (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case nil => intro _; exact Matches.refl _
  case snoc => intro he; simp at he
  case sub hs hm ih => intro he; exact (ih he).trans hm

theorem nil_iff {C : Context} {a b : List OpType} : SeqT C [] ⟨a, b⟩ ↔ Matches a b :=
  ⟨fun h => nil_inv h rfl, fun h => .sub .nil h⟩

private theorem last_inv {C : Context} {code : List Instr} {st : StackType}
    (h : SeqT C code st) : ∀ es e, code = es ++ [e] →
      ∃ p x y z, Matches (p ++ z) st.outs ∧ SeqT C es ⟨st.ins, p ++ x⟩ ∧
        Matches x y ∧ InstrT C e ⟨y, z⟩ := by
  induction h using SeqT.rec (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case nil => intro es e he; simp at he
  case snoc hs hm hi ihs ihi =>
    intro es e he
    obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp he
    exact ⟨_, _, _, _, Matches.refl _, hs, hm, hi⟩
  case sub hs hm ih =>
    intro es e he
    obtain ⟨p, x, y, z, hout, hs, hm', hi⟩ := ih es e he
    exact ⟨p, x, y, z, hout.trans hm, hs, hm', hi⟩

theorem snoc_iff {C : Context} {es : List Instr} {e : Instr} {a b : List OpType} :
    SeqT C (es ++ [e]) ⟨a, b⟩ ↔
      ∃ p x y z, Matches (p ++ z) b ∧ SeqT C es ⟨a, p ++ x⟩ ∧
        Matches x y ∧ InstrT C e ⟨y, z⟩ :=
  ⟨fun h => last_inv h es e rfl,
    fun ⟨_, _, _, _, hout, hs, hm, hi⟩ => .sub (.snoc hs hm hi) hout⟩

theorem append {C : Context} {xs ys : List Instr} {a b c : List OpType}
    (hx : SeqT C xs ⟨a, b⟩) (hy : SeqT C ys ⟨b, c⟩) : SeqT C (xs ++ ys) ⟨a, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => simpa only [List.append_nil] using SeqT.sub hx (nil_iff.mp hy)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp hy
    simpa only [List.append_assoc] using SeqT.sub (SeqT.snoc (ih hs) hm hi) hout

theorem split {C : Context} {xs ys : List Instr} {a c : List OpType}
    (h : SeqT C (xs ++ ys) ⟨a, c⟩) : ∃ b, SeqT C xs ⟨a, b⟩ ∧ SeqT C ys ⟨b, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => exact ⟨c, by simpa using h, .nil⟩
  | append_singleton es e ih =>
    rw [← List.append_assoc] at h
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    obtain ⟨b, hx, hy⟩ := ih hs
    exact ⟨b, hx, .sub (.snoc hy hm hi) hout⟩

theorem single {C : Context} {i : Instr} {a b : List OpType} (h : InstrT C i ⟨a, b⟩) :
    SeqT C [i] ⟨a, b⟩ := SeqT.snoc (t₀ := []) .nil (Matches.refl a) h

theorem frame {C : Context} {es : List Instr} {a b : List OpType}
    (h : SeqT C es ⟨a, b⟩) (p : List OpType) : SeqT C es ⟨p ++ a, p ++ b⟩ := by
  induction es using List.reverseRecOn generalizing b with
  | nil => exact nil_iff.mpr ((Matches.refl p).append (nil_iff.mp h))
  | append_singleton es e ih =>
    obtain ⟨q, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    apply SeqT.sub (t₂ := p ++ (q ++ z))
    · simpa only [List.append_assoc] using
        SeqT.snoc (t₀ := p ++ q) (by simpa only [List.append_assoc] using ih hs) hm hi
    · exact (Matches.refl p).append hout

end SeqT

namespace ASeqT

private theorem nil_inv {s : Store} {C : Context} {es : List AInstr} {st : StackType}
    (h : ASeqT s C es st) : es = [] → Matches st.ins st.outs := by
  induction h using ASeqT.rec (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case nil => intro _; exact Matches.refl _
  case snoc => intro he; simp at he
  case sub hs hm ih => intro he; exact (ih he).trans hm

theorem nil_iff {s : Store} {C : Context} {a b : List OpType} :
    ASeqT s C [] ⟨a, b⟩ ↔ Matches a b :=
  ⟨fun h => nil_inv h rfl, fun h => .sub .nil h⟩

private theorem last_inv {s : Store} {C : Context} {code : List AInstr} {st : StackType}
    (h : ASeqT s C code st) : ∀ es e, code = es ++ [e] →
      ∃ p x y z, Matches (p ++ z) st.outs ∧ ASeqT s C es ⟨st.ins, p ++ x⟩ ∧
        Matches x y ∧ AInstrT s C e ⟨y, z⟩ := by
  induction h using ASeqT.rec (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case nil => intro es e he; simp at he
  case snoc hs hm hi ihs ihi =>
    intro es e he
    obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp he
    exact ⟨_, _, _, _, Matches.refl _, hs, hm, hi⟩
  case sub hs hm ih =>
    intro es e he
    obtain ⟨p, x, y, z, hout, hs, hm', hi⟩ := ih es e he
    exact ⟨p, x, y, z, hout.trans hm, hs, hm', hi⟩

theorem snoc_iff {s : Store} {C : Context} {es : List AInstr} {e : AInstr}
    {a b : List OpType} : ASeqT s C (es ++ [e]) ⟨a, b⟩ ↔
      ∃ p x y z, Matches (p ++ z) b ∧ ASeqT s C es ⟨a, p ++ x⟩ ∧
        Matches x y ∧ AInstrT s C e ⟨y, z⟩ :=
  ⟨fun h => last_inv h es e rfl,
    fun ⟨_, _, _, _, hout, hs, hm, hi⟩ => .sub (.snoc hs hm hi) hout⟩

theorem append {s : Store} {C : Context} {xs ys : List AInstr} {a b c : List OpType}
    (hx : ASeqT s C xs ⟨a, b⟩) (hy : ASeqT s C ys ⟨b, c⟩) :
    ASeqT s C (xs ++ ys) ⟨a, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => simpa only [List.append_nil] using ASeqT.sub hx (nil_iff.mp hy)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp hy
    simpa only [List.append_assoc] using ASeqT.sub (ASeqT.snoc (ih hs) hm hi) hout

theorem split {s : Store} {C : Context} {xs ys : List AInstr} {a c : List OpType}
    (h : ASeqT s C (xs ++ ys) ⟨a, c⟩) :
    ∃ b, ASeqT s C xs ⟨a, b⟩ ∧ ASeqT s C ys ⟨b, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => exact ⟨c, by simpa using h, .nil⟩
  | append_singleton es e ih =>
    rw [← List.append_assoc] at h
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    obtain ⟨b, hx, hy⟩ := ih hs
    exact ⟨b, hx, .sub (.snoc hy hm hi) hout⟩

theorem single {s : Store} {C : Context} {i : AInstr} {a b : List OpType}
    (h : AInstrT s C i ⟨a, b⟩) : ASeqT s C [i] ⟨a, b⟩ :=
  ASeqT.snoc (t₀ := []) .nil (Matches.refl a) h

theorem frame {s : Store} {C : Context} {es : List AInstr} {a b : List OpType}
    (h : ASeqT s C es ⟨a, b⟩) (p : List OpType) : ASeqT s C es ⟨p ++ a, p ++ b⟩ := by
  induction es using List.reverseRecOn generalizing b with
  | nil => exact nil_iff.mpr ((Matches.refl p).append (nil_iff.mp h))
  | append_singleton es e ih =>
    obtain ⟨q, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    apply ASeqT.sub (t₂ := p ++ (q ++ z))
    · simpa only [List.append_assoc] using
        ASeqT.snoc (t₀ := p ++ q) (by simpa only [List.append_assoc] using ih hs) hm hi
    · exact (Matches.refl p).append hout

theorem input {s : Store} {C : Context} {es : List AInstr} {a b c : List OpType}
    (h : ASeqT s C es ⟨b, c⟩) (hm : Matches a b) : ASeqT s C es ⟨a, c⟩ :=
  (nil_iff.mpr hm).append h

theorem plain {s : Store} {C : Context} {es : List Instr} {a b : List OpType}
    (h : SeqT C es ⟨a, b⟩) : ASeqT s C (es.map .plain) ⟨a, b⟩ := by
  induction es using List.reverseRecOn generalizing b with
  | nil => exact nil_iff.mpr (SeqT.nil_iff.mp h)
  | append_singleton es e ih =>
    obtain ⟨q, x, y, z, hout, hs, hm, hi⟩ := SeqT.snoc_iff.mp h
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      ASeqT.sub (ASeqT.snoc (ih hs) hm (.plain hi)) hout

theorem single_iff {s : Store} {C : Context} {e : AInstr} {a b : List OpType} :
    ASeqT s C [e] ⟨a, b⟩ ↔ ∃ p x y z, Matches a (p ++ x) ∧ Matches (p ++ z) b ∧
      Matches x y ∧ AInstrT s C e ⟨y, z⟩ := by
  rw [show [e] = [] ++ [e] from rfl, snoc_iff]
  constructor
  · rintro ⟨p, x, y, z, hb, hs, hm, he⟩
    exact ⟨p, x, y, z, nil_iff.mp hs, hb, hm, he⟩
  · rintro ⟨p, x, y, z, ha, hb, hm, he⟩
    exact ⟨p, x, y, z, hb, nil_iff.mpr ha, hm, he⟩

theorem cons_iff {s : Store} {C : Context} {e : AInstr} {es : List AInstr}
    {a b : List OpType} : ASeqT s C (e :: es) ⟨a, b⟩ ↔
      ∃ p x y z, Matches a (p ++ x) ∧ Matches x y ∧ AInstrT s C e ⟨y, z⟩ ∧
        ASeqT s C es ⟨p ++ z, b⟩ := by
  constructor
  · intro h
    obtain ⟨c, he, hs⟩ := split (xs := [e]) (ys := es) h
    obtain ⟨p, x, y, z, ha, hout, hm, he⟩ := single_iff.mp he
    exact ⟨p, x, y, z, ha, hm, he, hs.input hout⟩
  · rintro ⟨p, x, y, z, ha, hm, he, hs⟩
    exact append (single_iff.mpr ⟨p, x, y, z, ha, Matches.refl _, hm, he⟩) hs

end ASeqT

namespace AInstrT

theorem value_inv {s : Store} {C : Context} {v : Val} {a b : List OpType}
    (h : AInstrT s C v.instr ⟨a, b⟩) :
    ∃ t, a = [] ∧ b = [.val t] ∧ v.HasType s t := by
  cases v with
  | i32 v => cases h with | plain h => cases h; exact ⟨_, rfl, rfl, trivial⟩
  | i64 v => cases h with | plain h => cases h; exact ⟨_, rfl, rfl, trivial⟩
  | f32 v => cases h with | plain h => cases h; exact ⟨_, rfl, rfl, trivial⟩
  | f64 v => cases h with | plain h => cases h; exact ⟨_, rfl, rfl, trivial⟩
  | ref r =>
    cases r with
    | null t => cases h with | plain h => cases h; exact ⟨_, rfl, rfl, rfl⟩
    | func a => cases h with | refFuncAddr h => exact ⟨_, rfl, rfl, h⟩
    | extern a => cases h; exact ⟨_, rfl, rfl, trivial⟩

theorem value {s : Store} {C : Context} {v : Val} {t : ValType} (h : v.HasType s t) :
    AInstrT s C v.instr ⟨[], [.val t]⟩ := by
  cases v with
  | i32 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .plain (.iconst v.isLt)
    | ref r => cases h
  | i64 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .plain (.iconst v.isLt)
    | ref r => cases h
  | f32 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .plain (.fconst v.isLt)
    | ref r => cases h
  | f64 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .plain (.fconst v.isLt)
    | ref r => cases h
  | ref r =>
    cases r with
    | null rt =>
      cases t with
      | num n => cases h
      | ref rt' => cases h; exact .plain .refNull
    | func a =>
      cases t with
      | num n => cases h
      | ref rt => cases rt with
        | funcref => exact .refFuncAddr h
        | externref => cases h
    | extern a =>
      cases t with
      | num n => cases h
      | ref rt => cases rt with
        | funcref => cases h
        | externref => exact .refExternAddr

end AInstrT

namespace ASeqT

theorem values_inv {s : Store} {C : Context} {vs : List Val} {a b : List OpType}
    (h : ASeqT s C (vals vs) ⟨a, b⟩) :
    ∃ ts, Matches (a ++ ops ts) b ∧ List.Forall₂ (Val.HasType s) vs ts := by
  induction vs using List.reverseRecOn generalizing b with
  | nil => exact ⟨[], by simpa [ops] using nil_iff.mp h, .nil⟩
  | append_singleton vs v ih =>
    change ASeqT s C ((vs ++ [v]).map Val.instr) _ at h
    rw [List.map_append] at h
    obtain ⟨p, x, y, z, hout, hs, hm, he⟩ := snoc_iff.mp h
    obtain ⟨t, rfl, rfl, hv⟩ := AInstrT.value_inv he
    have hx : x = [] := by cases hm; rfl
    subst x
    simp only [List.append_nil] at hs
    obtain ⟨ts, hprefix, hvs⟩ := ih hs
    refine ⟨ts ++ [t], ?_, List.rel_append hvs (.cons hv .nil)⟩
    simpa only [ops, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using
      (hprefix.append (Matches.refl [.val t])).trans hout

theorem values {s : Store} {C : Context} {vs : List Val} {ts : List ValType}
    (h : List.Forall₂ (Val.HasType s) vs ts) (p : List OpType := []) :
    ASeqT s C (vals vs) ⟨p, p ++ ops ts⟩ := by
  induction h generalizing p with
  | nil => simpa only [ops, List.map_nil, List.append_nil] using (ASeqT.nil (ts := p))
  | @cons v t vs ts hv hs ih =>
    have h₁ := (single (AInstrT.value (C := C) hv)).frame p
    have h₂ := ih (p ++ [.val t])
    simpa only [List.append_nil, List.append_assoc, List.singleton_append, ops,
      List.map_cons] using h₁.append h₂

theorem value_prefix_inv {s : Store} {C : Context} {vs : List Val} {es : List AInstr}
    {a b : List OpType} (h : ASeqT s C (vals vs ++ es) ⟨a, b⟩) :
    ∃ ts, List.Forall₂ (Val.HasType s) vs ts ∧ ASeqT s C es ⟨a ++ ops ts, b⟩ := by
  obtain ⟨c, hv, he⟩ := split h
  obtain ⟨ts, hm, hvs⟩ := values_inv hv
  exact ⟨ts, hvs, he.input hm⟩

end ASeqT

end FVA.Wasm.Valid
