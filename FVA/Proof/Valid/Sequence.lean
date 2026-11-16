import FVA.Spec.Valid.Soundness
import FVA.Proof.Valid.Seq

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem _root_.FVA.Wasm.Exec.Val.instr_sets' (v : Val) : v.instr.sets = [] := by
  cases v with
  | ref r => cases r <;> rfl
  | _ => rfl

theorem _root_.FVA.Wasm.Exec.Val.instr_dead' (v : Val) : v.instr.dead = false := by
  cases v with
  | ref r => cases r <;> rfl
  | _ => rfl

theorem ASeqT.vals_dead' (vs : List Val) : (vals vs).any AInstr.dead = false := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [vals, Val.instr_dead'] at ih ⊢

theorem ASeqT.vals_sets' (vs : List Val) : (vals vs).flatMap AInstr.sets = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    cases v with
    | ref r => cases r <;> rfl
    | _ => rfl

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
        Matches x y ∧ AInstrT s (C.after es) e ⟨y, z⟩ := by
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
        Matches x y ∧ AInstrT s (C.after es) e ⟨y, z⟩ :=
  ⟨fun h => last_inv h es e rfl,
    fun ⟨_, _, _, _, hout, hs, hm, hi⟩ => .sub (.snoc hs hm hi) hout⟩

theorem after_after (C : Context) (xs es : List AInstr) :
    (C.after xs).after es = C.after (xs ++ es) := by
  simp only [Context.after, Context.addSets, List.flatMap_append, List.reverse_append,
    List.append_assoc, List.any_append, Bool.or_assoc]

theorem _root_.FVA.Wasm.Valid.Context.after_nil (C : Context) : C.after [] = C := by
  simp only [Context.after, Context.addSets, List.flatMap_nil, List.reverse_nil, List.nil_append,
    List.any_nil, Bool.or_false]

theorem _root_.FVA.Wasm.Valid.Context.Entails.after {C D : Context} (h : C.Entails D)
    (es : List AInstr) : (C.after es).Entails (D.after es) := by
  have h1 := h.addSets (es.flatMap AInstr.sets)
  refine { h1 with locals := ?_, dead := ?_ }
  · intro x lt hx
    obtain ⟨lt', hx', ht, hr⟩ := h1.locals x lt hx
    refine ⟨lt', hx', ht, ?_⟩
    simp only [Context.after, Bool.or_eq_true] at hr ⊢
    rintro (h' | h' | h' | h')
    · rcases hr (.inl h') with h'' | h'' | h''
      · exact .inl h''
      · exact .inr (.inl h'')
      · exact .inr (.inr (.inl (by simpa [Context.addSets] using h'')))
    · rcases hr (.inr (.inl h')) with h'' | h'' | h''
      · exact .inl h''
      · exact .inr (.inl h'')
      · exact .inr (.inr (.inl (by simpa [Context.addSets] using h'')))
    · exact .inr (.inr (.inl (h.dead h')))
    · exact .inr (.inr (.inr h'))
  · simp only [Context.after, Bool.or_eq_true]
    rintro (h' | h')
    · exact .inl (h.dead h')
    · exact .inr h'

/-- What follows a fragment reads at least what the fragment's own context does. -/
theorem _root_.FVA.Wasm.Valid.Context.Entails.to_after (C : Context) (es : List AInstr) :
    C.Entails (C.after es) := by
  have h := (Context.Entails.refl C).addSets_mono (xs := []) (ys := es.flatMap AInstr.sets)
    (fun _ h => nomatch h)
  rw [Context.addSets_nil] at h
  refine { h with locals := ?_, dead := ?_ }
  · intro x lt hx
    obtain ⟨lt', hx', ht, hr⟩ := h.locals x lt hx
    refine ⟨lt', hx', ht, fun h' => ?_⟩
    rcases hr h' with h'' | h'' | h''
    · exact .inl h''
    · exact .inr (.inl h'')
    · exact .inr (.inr (by simp only [Context.addSets] at h''; simp [Context.after, h'']))
  · intro hd; simp [Context.after, hd]

theorem after_eq_addSets (C : Context) {es : List AInstr} (hd : es.any AInstr.dead = false) :
    C.after es = C.addSets (es.flatMap AInstr.sets) := by
  simp only [Context.after, Context.addSets, hd, Bool.or_false]

theorem _root_.FVA.Wasm.Valid.Context.Entails.to_addSets (C : Context) (xs : List Nat) :
    C.Entails (C.addSets xs) :=
  (Context.Entails.refl C).addSets_mono (xs := []) (fun _ h => nomatch h)

/-- After a dead end everything is readable: any context after a prefix entails it. -/
theorem _root_.FVA.Wasm.Valid.Context.Entails.to_dead_after (C : Context) (xs : List AInstr)
    {es : List AInstr} (hd : es.any AInstr.dead = true) : (C.after xs).Entails (C.after es) := by
  have hde : (C.after es).dead = true := by simp [Context.after, hd]
  refine ⟨rfl, rfl, rfl, fun _ tt h => ⟨tt, h, rfl⟩, fun _ lim h => ⟨lim, h⟩, rfl, rfl,
    Nat.le_refl _, fun x lt hx => ⟨lt, hx, rfl, fun _ => .inr (.inr hde)⟩, rfl, rfl,
    fun _ h => h, fun _ => hde⟩

theorem after_pure (C : Context) {xs : List AInstr} (hs : xs.flatMap AInstr.sets = [])
    (hd : xs.any AInstr.dead = false) : C.after xs = C := by
  simp only [Context.after, Context.addSets, hs, hd, List.reverse_nil, List.nil_append,
    Bool.or_false]

theorem append {s : Store} {C : Context} {xs ys : List AInstr} {a b c : List OpType}
    (hx : ASeqT s C xs ⟨a, b⟩) (hy : ASeqT s (C.after xs) ys ⟨b, c⟩) :
    ASeqT s C (xs ++ ys) ⟨a, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => simpa only [List.append_nil] using ASeqT.sub hx (nil_iff.mp hy)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp hy
    rw [after_after] at hi
    simpa only [List.append_assoc] using ASeqT.sub (ASeqT.snoc (ih hs) hm hi) hout

/-- `append` for a prefix without initializations (values, most instructions). -/
theorem append_pure {s : Store} {C : Context} {xs ys : List AInstr} {a b c : List OpType}
    (hx : ASeqT s C xs ⟨a, b⟩) (hy : ASeqT s C ys ⟨b, c⟩)
    (hp : xs.flatMap AInstr.sets = [] := by
      simp only [List.flatMap_append, ASeqT.vals_sets', List.flatMap_cons, List.flatMap_nil,
        Val.instr, Val.instr_sets', AInstr.sets, Instr.sets, List.append_nil, List.nil_append])
    (hd : xs.any AInstr.dead = false := by
      simp only [List.any_append, ASeqT.vals_dead', List.any_cons, List.any_nil, Val.instr,
        Val.instr_dead', AInstr.dead, Bool.or_false, Bool.false_or]) :
    ASeqT s C (xs ++ ys) ⟨a, c⟩ :=
  append hx (by rw [after_pure C hp hd]; exact hy)

theorem split {s : Store} {C : Context} {xs ys : List AInstr} {a c : List OpType}
    (h : ASeqT s C (xs ++ ys) ⟨a, c⟩) :
    ∃ b, ASeqT s C xs ⟨a, b⟩ ∧ ASeqT s (C.after xs) ys ⟨b, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => exact ⟨c, by simpa using h, .nil⟩
  | append_singleton es e ih =>
    rw [← List.append_assoc] at h
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    obtain ⟨b, hx, hy⟩ := ih hs
    rw [← after_after] at hi
    exact ⟨b, hx, .sub (.snoc hy hm hi) hout⟩

theorem single {s : Store} {C : Context} {i : AInstr} {a b : List OpType}
    (h : AInstrT s C i ⟨a, b⟩) : ASeqT s C [i] ⟨a, b⟩ :=
  ASeqT.snoc (t₀ := []) .nil (Matches.refl a) (by rw [Context.after_nil]; exact h)

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
  (nil_iff.mpr hm).append (by rw [Context.after_nil]; exact h)

theorem sets_plain (es : List Instr) :
    (es.map .plain).flatMap AInstr.sets = es.flatMap Instr.sets := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, List.flatMap_cons, AInstr.sets, ih]

theorem plain {s : Store} {C : Context} {es : List Instr} {a b : List OpType}
    (h : SeqT C es ⟨a, b⟩) : ASeqT s C (es.map .plain) ⟨a, b⟩ := by
  induction es using List.reverseRecOn generalizing b with
  | nil => exact nil_iff.mpr (SeqT.nil_iff.mp h)
  | append_singleton es e ih =>
    obtain ⟨q, x, y, z, hout, hs, hm, hi⟩ := SeqT.snoc_iff.mp h
    have hent : (C.addSets (es.flatMap Instr.sets)).Entails (C.after (es.map .plain)) := by
      have he := (Context.Entails.refl (C.addSets (es.flatMap Instr.sets)))
      refine { he with locals := ?_, dead := fun hd => ?_ }
      · intro x lt hx
        refine ⟨lt, ?_, rfl, ?_⟩
        · simpa [Context.after, Context.addSets] using hx
        · rintro (h' | h' | h')
          · exact .inl h'
          · exact .inr (.inl (by simpa [Context.after, Context.addSets, sets_plain] using h'))
          · exact .inr (.inr (by simp [Context.after, Context.addSets] at h' ⊢; simp [h']))
      · simp [Context.after, Context.addSets] at hd ⊢; simp [hd]
    have hi' : AInstrT s (C.after (es.map .plain)) (.plain e) ⟨y, z⟩ := .plain (hi.transport hent)
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      ASeqT.sub (ASeqT.snoc (ih hs) hm hi') hout

theorem single_iff {s : Store} {C : Context} {e : AInstr} {a b : List OpType} :
    ASeqT s C [e] ⟨a, b⟩ ↔ ∃ p x y z, Matches a (p ++ x) ∧ Matches (p ++ z) b ∧
      Matches x y ∧ AInstrT s C e ⟨y, z⟩ := by
  rw [show [e] = [] ++ [e] from rfl, snoc_iff]
  constructor
  · rintro ⟨p, x, y, z, hb, hs, hm, he⟩
    exact ⟨p, x, y, z, nil_iff.mp hs, hb, hm, by rwa [Context.after_nil] at he⟩
  · rintro ⟨p, x, y, z, ha, hb, hm, he⟩
    exact ⟨p, x, y, z, hb, nil_iff.mpr ha, hm, by rwa [Context.after_nil]⟩

theorem cons_iff {s : Store} {C : Context} {e : AInstr} {es : List AInstr}
    {a b : List OpType} : ASeqT s C (e :: es) ⟨a, b⟩ ↔
      ∃ p x y z, Matches a (p ++ x) ∧ Matches x y ∧ AInstrT s C e ⟨y, z⟩ ∧
        ASeqT s (C.after [e]) es ⟨p ++ z, b⟩ := by
  constructor
  · intro h
    obtain ⟨c, he, hs⟩ := split (xs := [e]) (ys := es) h
    obtain ⟨p, x, y, z, ha, hout, hm, he⟩ := single_iff.mp he
    exact ⟨p, x, y, z, ha, hm, he, by simpa using hs.input hout⟩
  · rintro ⟨p, x, y, z, ha, hm, he, hs⟩
    exact append (single_iff.mpr ⟨p, x, y, z, ha, Matches.refl _, hm, he⟩) (by simpa using hs)

end ASeqT

theorem _root_.FVA.Wasm.Exec.Val.instr_sets (v : Val) : v.instr.sets = [] := by
  cases v with
  | ref r => cases r <;> rfl
  | _ => rfl

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
    | null => cases h with | refNullAddr => exact ⟨_, rfl, rfl, rfl⟩
    | func a =>
      cases h with
      | refFuncAddr h => exact ⟨_, rfl, rfl, _, h, ValType.Sub.refl _⟩
    | extern a => cases h; exact ⟨_, rfl, rfl, rfl⟩
    | exn a => cases h with | refExnAddr h => exact ⟨_, rfl, rfl, h, rfl⟩

/-- A value instruction at any type its value has (its own type, widened). -/
theorem value {s : Store} {C : Context} {v : Val} {t : ValType} (h : v.HasType s t) :
    ASeqT s C [v.instr] ⟨[], [.val t]⟩ := by
  cases v with
  | i32 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .single (.plain (.iconst v.isLt))
    | ref r => cases h
  | i64 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .single (.plain (.iconst v.isLt))
    | ref r => cases h
  | f32 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .single (.plain (.fconst v.isLt))
    | ref r => cases h
  | f64 v =>
    cases t with
    | num n => cases n <;> simp_all [Val.HasType]; exact .single (.plain (.fconst v.isLt))
    | ref r => cases h
  | ref r =>
    cases t with
    | num n => cases r <;> cases h
    | ref rt =>
      rcases rt with ⟨n, ht⟩
      cases r with
      | null =>
        cases n with
        | false => cases h
        | true => exact .single .refNullAddr
      | func a =>
        obtain ⟨fi, hfi, hsub⟩ := h
        exact .sub (.single (.refFuncAddr hfi)) (.cons hsub .nil)
      | extern a =>
        simp only [Val.HasType] at h
        subst h
        exact .sub (.single .refExternAddr)
          (.cons (by simp [OpType.Matches, ValType.Sub]) .nil)
      | exn a =>
        obtain ⟨ha, hh⟩ := h
        simp only at hh
        subst hh
        exact .sub (.single (.refExnAddr ha))
          (.cons (by simp [OpType.Matches, ValType.Sub]) .nil)

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
    have h₁ := (AInstrT.value (C := C) hv).frame p
    have h₂ := ih (p ++ [.val t])
    have :=
      h₁.append_pure (ys := vals vs) h₂ (by simp [Val.instr_sets']) (by simp [Val.instr_dead'])
    simpa only [List.append_nil, List.append_assoc, List.singleton_append, ops,
      List.map_cons] using this

theorem vals_sets (vs : List Val) : (vals vs).flatMap AInstr.sets = [] := by
  simp [vals, Val.instr_sets]

theorem value_prefix_inv {s : Store} {C : Context} {vs : List Val} {es : List AInstr}
    {a b : List OpType} (h : ASeqT s C (vals vs ++ es) ⟨a, b⟩) :
    ∃ ts, List.Forall₂ (Val.HasType s) vs ts ∧ ASeqT s C es ⟨a ++ ops ts, b⟩ := by
  obtain ⟨c, hv, he⟩ := split h
  obtain ⟨ts, hm, hvs⟩ := values_inv hv
  rw [after_pure C (ASeqT.vals_sets' vs) (ASeqT.vals_dead' vs)] at he
  exact ⟨ts, hvs, he.input hm⟩

/-- A pending throw is typed at any stack type (it never falls through). -/
theorem throwing_typed {s : Store} {C : Context} {a : Nat} (h : a < s.exns.length)
    (x y : List OpType) : ASeqT s C (throwing a) ⟨x, y⟩ := by
  have h1 := (ASeqT.single (s := s) (C := C) (AInstrT.refExnAddr h)).frame x
  simp only [List.append_nil] at h1
  have hm : Matches (x ++ [.val (.ref ⟨false, .abs .exn⟩)]) (x ++ [.val (.ref .exnref)]) :=
    (Matches.refl x).append (.cons ⟨fun _ => rfl, .inl rfl⟩ .nil)
  have h2 := ASeqT.snoc (t₀ := []) (by simpa using h1) hm
    (AInstrT.plain (C := C.after [.refExnAddr a]) (InstrT.throwRef (t₁ := x) (t₂ := y)))
  simpa using h2

end ASeqT

end FVA.Wasm.Valid
