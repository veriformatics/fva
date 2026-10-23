import FVA.Proof.Valid.Numeric
import FVA.Proof.Valid.Updates

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

theorem Matches.append_inv {a b c d : List OpType} (h : Matches (a ++ b) (c ++ d))
    (hlen : b.length = d.length) : Matches a c ∧ Matches b d := by
  have hprefix : a.length = c.length := by
    have := h.length_eq
    simp only [List.length_append] at this
    omega
  constructor
  · have ht := List.forall₂_take a.length h
    rw [List.take_left, hprefix, List.take_left] at ht
    exact ht
  · have ht := List.forall₂_drop a.length h
    rw [List.drop_left, hprefix, List.drop_left] at ht
    exact ht

theorem hasOp_ops {s : Store} {vs : List Val} {ts : List ValType}
    (h : List.Forall₂ (Val.HasType s) vs ts) : List.Forall₂ (HasOpType s) vs (ops ts) :=
  List.forall₂_map_right_iff.mpr h

theorem ASeqT.fixed_arity_inv {s : Store} {C : Context} {vs : List Val} {e : AInstr}
    {a b : List OpType} (h : ASeqT s C (vals vs ++ [e]) ⟨a, b⟩)
    (arity : ∀ {x y}, AInstrT s C e ⟨x, y⟩ → vs.length = x.length) :
    ∃ p x y, Matches a p ∧ Matches (p ++ y) b ∧ AInstrT s C e ⟨x, y⟩ ∧
      List.Forall₂ (HasOpType s) vs x := by
  obtain ⟨p, x, y, z, hout, hs, hm, he⟩ := snoc_iff.mp h
  obtain ⟨ts, hmatch, hvs⟩ := values_inv hs
  have hfull := hmatch.trans ((Matches.refl p).append hm)
  have hlen : (ops ts).length = y.length := by
    simpa only [ops, List.length_map, ← hvs.length_eq] using arity he
  obtain ⟨hp, ht⟩ := hfull.append_inv hlen
  have hty := Matches.of_ops ht
  exact ⟨p, y, z, hp, hout, he, hty.symm ▸ hasOp_ops hvs⟩

theorem ASeqT.replace_fixed {s : Store} {C : Context} {vs : List Val} {e : AInstr}
    {a b : List OpType} {out : List AInstr} (h : ASeqT s C (vals vs ++ [e]) ⟨a, b⟩)
    (arity : ∀ {x y}, AInstrT s C e ⟨x, y⟩ → vs.length = x.length)
    (replacement : ∀ {x y}, AInstrT s C e ⟨x, y⟩ → List.Forall₂ (HasOpType s) vs x →
      ASeqT s C out ⟨[], y⟩) : ASeqT s C out ⟨a, b⟩ := by
  obtain ⟨p, x, y, hp, hout, he, hvs⟩ := h.fixed_arity_inv arity
  have hnew : ASeqT s C out ⟨p, p ++ y⟩ := by
    simpa only [List.append_nil] using (replacement he hvs).frame p
  exact .sub (hnew.input hp) hout

theorem ASeqT.hasOp_value {s : Store} {C : Context} {v : Val} {t : OpType}
    (h : HasOpType s v t) : ASeqT s C [v.instr] ⟨[], [t]⟩ := by
  cases t with
  | bot => cases h
  | val t => exact .single (.value h)

theorem ASeqT.numeric {s : Store} {C : Context} {vs : List Val} {i : Instr}
    {a b : List OpType} {r : Option Val} (h : ASeqT s C (vals vs ++ [.plain i]) ⟨a, b⟩)
    (hr : r ∈ numResults i vs) :
    ASeqT s C (numOut r) ⟨a, b⟩ := by
  apply h.replace_fixed
  · intro x y hi
    cases hi with | plain hi => exact numResults_arity hi hr
  · intro x y hi _
    cases hi with | plain hi => exact (numResults_typed hi hr).output

theorem ASeqT.drop {s : Store} {C : Context} {v : Val} {a b : List OpType}
    (h : ASeqT s C [v.instr, .plain .drop] ⟨a, b⟩) : ASeqT s C [] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [v])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .nil

theorem ASeqT.select {s : Store} {C : Context} {v₁ v₂ : Val} {c : BitVec 32}
    {ts : Option (List ValType)} {a b : List OpType}
    (h : ASeqT s C [v₁.instr, v₂.instr, (Val.i32 c).instr, .plain (.select ts)] ⟨a, b⟩) :
    ASeqT s C [(if c ≠ 0 then v₁ else v₂).instr] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [v₁, v₂, .i32 c])
  · intro x y hi
    cases hi with | plain hi => cases hi <;> rfl
  · intro x y hi hvs
    cases hi with | plain hi =>
      cases hi <;>
        cases hvs with | cons h₁ hs =>
          cases hs with | cons h₂ hs =>
            split <;> exact .hasOp_value (by assumption)

theorem ASeqT.refIsNull {s : Store} {C : Context} {r : Ref} {a b : List OpType}
    (h : ASeqT s C [(Val.ref r).instr, .plain .refIsNull] ⟨a, b⟩) :
    ASeqT s C [vi32 (if r.isNull then 1 else 0)] ⟨a, b⟩ := by
  apply h.replace_fixed (vs := [.ref r])
  · intro x y hi
    cases hi with | plain hi => cases hi; rfl
  · intro x y hi _
    cases hi with | plain hi => cases hi; exact .single (.value trivial)

end FVA.Wasm.Valid
