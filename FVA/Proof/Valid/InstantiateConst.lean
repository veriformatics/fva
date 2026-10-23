import FVA.Proof.Valid.Store
import FVA.Proof.Exec.Det

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

namespace InitProof

theorem const_shape {C : Context} {i : Instr} {st : StackType}
    (hi : InstrT C i st) (hc : ConstInstr C i) :
    ∃ t, st.ins = [] ∧ st.outs = [.val t] := by
  cases hi <;> simp only [ConstInstr] at hc
  all_goals exact ⟨_, rfl, rfl⟩

theorem const_length {C : Context} {e : Expr} {st : StackType}
    (he : SeqT C e st) (hc : ConstExpr C e) : st.outs.length = st.ins.length + e.length := by
  induction he using SeqT.rec (motive_1 := fun _ _ _ _ => True) <;> try trivial
  case snoc hs hm hi ih _ =>
    have hc' : ConstExpr _ _ := fun i h => hc i (List.mem_append_left _ h)
    have hci := hc _ (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨t, hin, hout⟩ := const_shape hi hci
    have hlen := Matches.length_eq hm
    have hseq := ih hc'
    simp_all only [List.length_append, List.length_singleton, List.length_nil]
    omega
  case sub hs hm ih =>
    have hlen := Matches.length_eq hm
    exact hlen.symm.trans (ih hc)

theorem const_singleton {C : Context} {e : Expr} {t : ValType}
    (he : ExprT C e [t]) (hc : ConstExpr C e) :
    ∃ i, e = [i] ∧ ConstInstr C i ∧ InstrT C i ⟨[], [.val t]⟩ := by
  obtain ⟨out, hs, hm⟩ := he
  have he_len : e.length = 1 := by
    have hlen := const_length hs hc
    have hm' := Matches.length_eq hm
    simpa [ops] using hlen.symm.trans hm'
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp he_len
  have hci := hc i (by simp)
  obtain ⟨p, x, y, z, ho, hn, hm', hi⟩ := (SeqT.snoc_iff (es := []) (e := i)).mp hs
  have heq : p ++ x = [] := by
    have hnil := Matches.length_eq (SeqT.nil_iff.mp hn)
    exact List.eq_nil_of_length_eq_zero hnil.symm
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp heq
  have hty := ho.trans hm
  obtain ⟨u, hy, hz⟩ := const_shape hi hci
  dsimp at hy hz
  subst y z
  have hut : u = t := by
    have ht := Matches.of_ops (ts := [u]) (by simpa [ops] using hty)
    simpa [ops] using ht.symm
  subst u
  exact ⟨i, rfl, hci, hi⟩

theorem no_step_values {H : HostSem} {s : Store} {f : Frame} {vs : List Val} {c : Config} :
    ¬Step H ⟨s, f, vals vs⟩ c := by
  intro hs
  have hu : Ref.seqUnique s f [] (vals vs ++ []) = true := by
    rw [Ref.seqUnique_vals]
    rfl
  have hc := Ref.seq_complete hs [] [] hu
  simp [Ref.seq_values] at hc

theorem steps_values {H : HostSem} {s : Store} {f : Frame} {vs : List Val} {c : Config}
    (h : Steps H ⟨s, f, vals vs⟩ c) : c = ⟨s, f, vals vs⟩ := by
  induction h with
  | refl => rfl
  | tail h hs ih =>
    subst_vars
    exact False.elim (no_step_values hs)

theorem value_inj {v w : Val} (h : v.instr = w.instr) : v = w := by
  have hv := congrArg Ref.toVal h
  simpa only [Ref.toVal_instr, Option.some.injEq] using hv

theorem value_of_step {H : HostSem} {c : Config} {s : Store} {f : Frame} {v w : Val}
    (hs : Ref.step c = some ⟨s, f, [w.instr]⟩) (hu : Ref.uniqueStep c = true)
    (h : Steps H c ⟨s, f, [v.instr]⟩) : v = w := by
  rcases h.cases_head with hc | ⟨mid, h₀, hrest⟩
  · subst c
    exact False.elim (no_step_values (vs := [v]) (Ref.step_sound (H := H) hs))
  · have hmid := Ref.step_complete h₀ hs hu
    subst mid
    have hv := congrArg Config.instrs (steps_values (vs := [w]) hrest)
    exact value_inj (List.singleton_inj.mp hv)

/-- Initializer values need only the imported globals and the allocated function addresses;
validity of the allocated store is not an assumption. -/
theorem constant_value {H : HostSem} {s : Store} {inst : ModuleInst} {C : Context}
    (funcs : ∀ (x : Nat) (ft : FuncType), C.funcs[x]? = some ft →
      ∃ a, inst.funcs[x]? = some a ∧ a < s.funcs.length)
    (globals : ∀ (x : Nat) (gt : GlobalType), C.globals[x]? = some gt →
      ∃ (a : Nat) (gi : GlobalInst), inst.globals[x]? = some a ∧ s.globals[a]? = some gi ∧
        gi.value.HasType s gt.val)
    {e : Expr} {t : ValType} {v : Val} (he : ExprT C e [t]) (hc : ConstExpr C e)
    (steps : Steps H ⟨s, ⟨[], inst⟩, e.map .plain⟩ ⟨s, ⟨[], inst⟩, [v.instr]⟩) :
    v.HasType s t := by
  obtain ⟨i, rfl, hci, hi⟩ := const_singleton he hc
  cases i <;> simp only [ConstInstr] at hci
  case iconst w n =>
    cases hi
    rename_i hn
    cases w with
    | w32 =>
      let w : Val := .i32 ⟨n, hn⟩
      have hv := congrArg Config.instrs (steps_values (vs := [w]) steps)
      have heq : v = w := value_inj (List.singleton_inj.mp hv)
      simpa [heq, w, Val.HasType]
    | w64 =>
      let w : Val := .i64 ⟨n, hn⟩
      have hv := congrArg Config.instrs (steps_values (vs := [w]) steps)
      have heq : v = w := value_inj (List.singleton_inj.mp hv)
      simpa [heq, w, Val.HasType]
  case fconst w n =>
    cases hi
    rename_i hn
    cases w with
    | w32 =>
      let w : Val := .f32 ⟨n, hn⟩
      have hv := congrArg Config.instrs (steps_values (vs := [w]) steps)
      have heq : v = w := value_inj (List.singleton_inj.mp hv)
      simpa [heq, w, Val.HasType]
    | w64 =>
      let w : Val := .f64 ⟨n, hn⟩
      have hv := congrArg Config.instrs (steps_values (vs := [w]) steps)
      have heq : v = w := value_inj (List.singleton_inj.mp hv)
      simpa [heq, w, Val.HasType]
  case refNull rt =>
    cases hi
    have hv := congrArg Config.instrs (steps_values (vs := [.ref (.null rt)]) steps)
    have heq : v = .ref (.null rt) := value_inj (List.singleton_inj.mp hv)
    simp [heq, Val.HasType]
  case refFunc x =>
    cases hi
    rename_i ft hf hr
    obtain ⟨a, ha, hb⟩ := funcs x ft hf
    have hs : Ref.step ⟨s, ⟨[], inst⟩, [.plain (.refFunc x)]⟩ =
        some ⟨s, ⟨[], inst⟩, [(Val.ref (.func a)).instr]⟩ := by
      simp [Ref.step, Ref.seq, Ref.toVal, Ref.atInstr, Ref.instrStep, ha, Val.instr]
    have hu : Ref.uniqueStep ⟨s, ⟨[], inst⟩, [.plain (.refFunc x)]⟩ = true := by
      simp [Ref.uniqueStep, Ref.seqUnique, Ref.toVal, Ref.atUnique, Ref.instrUnique]
    have hv := value_of_step hs hu steps
    simpa [hv, Val.HasType] using hb
  case globalGet x =>
    cases hi
    rename_i gt hg
    obtain ⟨a, gi, ha, hgi, hval⟩ := globals x gt hg
    have hs : Ref.step ⟨s, ⟨[], inst⟩, [.plain (.globalGet x)]⟩ =
        some ⟨s, ⟨[], inst⟩, [gi.value.instr]⟩ := by
      simp [Ref.step, Ref.seq, Ref.toVal, Ref.atInstr, Ref.instrStep, ha, hgi]
    have hu : Ref.uniqueStep ⟨s, ⟨[], inst⟩, [.plain (.globalGet x)]⟩ = true := by
      simp [Ref.uniqueStep, Ref.seqUnique, Ref.toVal, Ref.atUnique, Ref.instrUnique]
    simpa [value_of_step hs hu steps] using hval

end InitProof
end FVA.Wasm.Valid
