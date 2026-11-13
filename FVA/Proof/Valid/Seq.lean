import FVA.Proof.Valid.Entails

/-!
# Operand matching and instruction sequences (static)

Matching is a preorder (subtyping of closed value types, bottom below everything, the bottom
reference below every reference type); sequence derivations split and compose, the later part
typed with the locals the earlier part initializes.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

theorem _root_.FVA.Wasm.ValType.Sub.refl (t : ValType) : t.Sub t := by
  cases t with
  | num _ => rfl
  | ref _ => exact ⟨id, .inl rfl⟩

theorem _root_.FVA.Wasm.ValType.Sub.trans {a b c : ValType} (h₁ : a.Sub b) (h₂ : b.Sub c) :
    a.Sub c := by
  cases a <;> cases b <;> cases c <;> simp only [ValType.Sub] at h₁ h₂ ⊢
  case num.num.num => exact h₁.trans h₂
  case ref.ref.ref r₁ r₂ r₃ =>
    obtain ⟨hn₁, hh₁⟩ := h₁
    obtain ⟨hn₂, hh₂⟩ := h₂
    refine ⟨fun h => hn₂ (hn₁ h), ?_⟩
    rcases hh₁ with he₁ | ⟨d, hd₁, hf₁⟩
    · rcases hh₂ with he₂ | ⟨d', hd₂, hf₂⟩
      · exact .inl (he₁.trans he₂)
      · exact .inr ⟨d', he₁.trans hd₂, hf₂⟩
    · rcases hh₂ with he₂ | ⟨d', hd₂, hf₂⟩
      · exact .inr ⟨d, hd₁, he₂ ▸ hf₁⟩
      · rw [hf₁] at hd₂
        cases hd₂

namespace OpType.Matches

theorem refl (t : OpType) : t.Matches t := by
  cases t with
  | bot | refBot => trivial
  | val t => exact ValType.Sub.refl t

theorem trans {a b c : OpType} (h₁ : a.Matches b) (h₂ : b.Matches c) : a.Matches c := by
  cases a with
  | bot => trivial
  | refBot =>
    cases b with
    | bot => exact h₁.elim
    | refBot => exact h₂
    | val u =>
      cases u with
      | num _ => exact h₁.elim
      | ref r =>
        cases c with
        | val w =>
          cases w with
          | num _ => exact h₂.elim
          | ref _ => trivial
        | _ => exact h₂.elim
  | val t =>
    cases b with
    | val u =>
      cases c with
      | val w => exact ValType.Sub.trans h₁ h₂
      | _ => exact h₂.elim
    | _ => exact h₁.elim

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

theorem of_sub {ts us : List ValType} (h : ResultSub ts us) :
    Matches (Valid.ops ts) (Valid.ops us) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

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
        Matches x y ∧ InstrT (C.addSets (es.flatMap Instr.sets)) e ⟨y, z⟩ := by
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
        Matches x y ∧ InstrT (C.addSets (es.flatMap Instr.sets)) e ⟨y, z⟩ :=
  ⟨fun h => last_inv h es e rfl,
    fun ⟨_, _, _, _, hout, hs, hm, hi⟩ => .sub (.snoc hs hm hi) hout⟩

/-- The context after `xs`: its initializations added. -/
theorem addSets_flatMap (C : Context) (xs es : List Instr) :
    (C.addSets (xs.flatMap Instr.sets)).addSets (es.flatMap Instr.sets) =
      C.addSets ((xs ++ es).flatMap Instr.sets) := by
  rw [Context.addSets_addSets, List.flatMap_append]

theorem append {C : Context} {xs ys : List Instr} {a b c : List OpType}
    (hx : SeqT C xs ⟨a, b⟩) (hy : SeqT (C.addSets (xs.flatMap Instr.sets)) ys ⟨b, c⟩) :
    SeqT C (xs ++ ys) ⟨a, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => simpa only [List.append_nil] using SeqT.sub hx (nil_iff.mp hy)
  | append_singleton es e ih =>
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp hy
    rw [addSets_flatMap] at hi
    simpa only [List.append_assoc] using SeqT.sub (SeqT.snoc (ih hs) hm hi) hout

theorem split {C : Context} {xs ys : List Instr} {a c : List OpType}
    (h : SeqT C (xs ++ ys) ⟨a, c⟩) :
    ∃ b, SeqT C xs ⟨a, b⟩ ∧ SeqT (C.addSets (xs.flatMap Instr.sets)) ys ⟨b, c⟩ := by
  induction ys using List.reverseRecOn generalizing c with
  | nil => exact ⟨c, by simpa using h, .nil⟩
  | append_singleton es e ih =>
    rw [← List.append_assoc] at h
    obtain ⟨p, x, y, z, hout, hs, hm, hi⟩ := snoc_iff.mp h
    obtain ⟨b, hx, hy⟩ := ih hs
    rw [← addSets_flatMap] at hi
    exact ⟨b, hx, .sub (.snoc hy hm hi) hout⟩

theorem single {C : Context} {i : Instr} {a b : List OpType} (h : InstrT C i ⟨a, b⟩) :
    SeqT C [i] ⟨a, b⟩ :=
  SeqT.snoc (t₀ := []) (is := []) .nil (Matches.refl a)
    (h.transport (by simpa only [List.flatMap_nil] using Context.Entails.addSets_nil C))

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

end FVA.Wasm.Valid
