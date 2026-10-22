import FVA.Impl.Exec.Det
import FVA.Proof.Exec.DetLemmas

/-!
# Deterministic steps and total-correctness claims from the stepper

Every executable step outside the choice points `uniqueStep` excludes (`FVA.Impl.Exec.Det`) is
the spec's only step; trap propagation keeps the store and ends at the same trap; `runDet`'s
final states are the outcome of every execution (`runDet_must`).
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

theorem seqUnique_vals (s : Store) (f : Frame) (vs ws : List Val) (es : List AInstr) :
    seqUnique s f vs (vals ws ++ es) = seqUnique s f (ws.reverse ++ vs) es := by
  induction ws generalizing vs with
  | nil => rfl
  | cons w ws ih =>
    simp only [vals, List.map_cons, List.cons_append, seqUnique, toVal_instr]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem seqTraps_vals (vs : List Val) (es : List AInstr) :
    seqTraps (vals vs ++ es) = seqTraps es := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, List.cons_append, seqTraps, toVal_instr, ih]

theorem num_instr_complete {i : Instr} {args : List Val} {r : Option Val}
    (s : Store) (f : Frame) (stk : List Val) (hr : r ∈ numResults i args)
    (hu : instrUnique i (args.reverse ++ stk) = true) :
    instrStep s f i (args.reverse ++ stk) = some (s, f, stk, numOut r) := by
  unfold numResults at hr
  split at hr
  all_goals try contradiction
  all_goals try
    change r = _ at hr
    subst r
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      instrStep, numStep, Option.map_some, implRel_eq, implTrunc_eq, implTruncSat_eq]
  all_goals obtain ⟨z, hz, rfl⟩ := hr
  all_goals simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    instrUnique, numUnique, numStep, r32, r64, Bool.not_eq_true'] at hu
  case h_9 =>
    rw [implUn_unique f32fmt_wide (ofBits_wf f32fmt_sane _) _ hz hu]
    rfl
  case h_10 =>
    rw [implUn_unique f64fmt_wide (ofBits_wf f64fmt_sane _) _ hz hu]
    rfl
  case h_11 =>
    rw [implBin_unique f32fmt_sane (ofBits_wf f32fmt_sane _)
      (ofBits_wf f32fmt_sane _) _ hz hu]
    rfl
  case h_12 =>
    rw [implBin_unique f64fmt_sane (ofBits_wf f64fmt_sane _)
      (ofBits_wf f64fmt_sane _) _ hz hu]
    rfl
  case h_26 =>
    rw [implConvert_unique f32fmt_sane _ _ hz hu]
    rfl
  case h_27 =>
    rw [implConvert_unique f32fmt_sane _ _ hz hu]
    rfl
  case h_28 =>
    rw [implConvert_unique f64fmt_sane _ _ hz hu]
    rfl
  case h_29 =>
    rw [implConvert_unique f64fmt_sane _ _ hz hu]
    rfl
  case h_30 =>
    rw [implDemote_unique (ofBits_wf f64fmt_sane _) hz hu]
    rfl
  case h_31 =>
    rw [implPromote_unique (ofBits_wf f32fmt_sane _) hz hu]
    rfl

theorem seqUnique_eval_trap (s : Store) (f : Frame) (E : EvalCtx) :
    ∀ (stk : List Val) (rest : List AInstr),
      seqUnique s f stk (E.fill [.trap] ++ rest) = false := by
  induction E with
  | hole => intro stk rest; rfl
  | seq vs inner tail ih =>
    intro stk rest
    simp only [EvalCtx.fill, List.append_assoc, seqUnique_vals]
    exact ih _ _
  | label n cont inner ih =>
    intro stk rest
    simp only [EvalCtx.fill, List.singleton_append, seqUnique, toVal, atUnique]
    simpa only [List.append_nil] using ih [] []

set_option maxHeartbeats 1000000 in
theorem seq_complete {H : HostSem} {c c' : Config} (h : Step H c c') :
    ∀ (stk : List Val) (rest : List AInstr),
      seqUnique c.store c.frame stk (c.instrs ++ rest) = true →
      seq c.store c.frame stk (c.instrs ++ rest) =
          .step c'.store c'.frame (vals stk.reverse ++ c'.instrs ++ rest) ∨
        seq c.store c.frame stk (c.instrs ++ rest) = .stuck := by
  induction h
  all_goals intro stk rest hu
  case num s f i args r hr =>
    have hn := num_toVal_none hr
    simp only [List.append_assoc, seqUnique_vals, List.singleton_append, seqUnique,
      hn, atUnique] at hu
    left
    rw [List.append_assoc, seq_vals]
    simp only [List.singleton_append, seq, hn]
    exact atInstr_plain_of_step rest (num_instr_complete s f stk hr hu)
  case refIsNull | refFunc | drop | select | localGet | localSet | localTee | globalGet |
      globalSet | tableGet | tableGetTrap | tableSet | tableSetTrap | tableSize | elemDrop |
      load | loadTrap | loadPacked | loadPackedTrap | store | storeTrap | storePacked |
      storePackedTrap | memorySize | dataDrop | nop | unreachable | ifTrue | ifFalse |
      brIfTrue | brIfFalse | brTable | call =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, tableAt, mem0, Bool.cond_eq_ite, Nat.blt_eq]
    all_goals split_ifs <;> first | omega | simp_all
  case tableFillTrap | tableFillZero | tableFill | tableCopyZero | tableCopyUp | tableCopyDown |
      tableInitZero | tableInit | memoryFillTrap | memoryFillZero | memoryFill |
      memoryCopyTrap | memoryCopyZero | memoryCopyUp | memoryCopyDown |
      memoryInitZero | memoryInit =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, tableAt, mem0, Bool.cond_eq_ite, Nat.blt_eq,
      Nat.beq_eq, Nat.ble_eq]
    all_goals split_ifs <;> first | omega | simp_all
  case tableGrow | tableGrowFail | memoryGrow | memoryGrowFail | invokeHost |
      invokeHostTrap | invokeHostDiverge | trapFrame =>
    simp only [List.append_assoc, seqUnique_vals, List.cons_append, List.nil_append,
      seqUnique, toVal_instr] at hu
    simp_all [toVal, seqUnique, atUnique, instrUnique]
  case trap s f E hne =>
    have ht := seqUnique_eval_trap s f E stk rest
    rw [ht] at hu
    contradiction
  case block s f bt body ft vs hft hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr,
      instrStep, hft, Option.bind_some]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, stack_drop, List.reverse_reverse]
    simp
  case loop s f bt body ft vs hft hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr,
      instrStep, hft, Option.bind_some]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, stack_drop, List.reverse_reverse]
    simp
  case invoke s f a ft inst code vs hf hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr, hf]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, stack_drop, List.reverse_reverse]
    simp
  case labelExit =>
    left
    simp [seq, toVal, atInstr, seq_values, isTrapOnly_vals, List.append_assoc]
  case frameExit =>
    left
    simp_all [seq, toVal, atInstr, seq_values, isTrapOnly_vals, Bool.cond_eq_ite]
  case seq s f s' f' es es' vs tail h ih =>
    simp only [List.append_assoc, seqUnique_vals] at hu
    simp only [List.append_assoc, seq_vals]
    rcases ih (vs.reverse ++ stk) (tail ++ rest) hu with hs | hs
    · left
      simpa only [List.reverse_append, List.reverse_reverse, List.map_append,
        List.append_assoc] using hs
    · exact Or.inr hs
  case label s f s' f' n cont es es' h ih =>
    simp only [List.singleton_append, seqUnique, toVal, atUnique] at hu
    have hh := ih [] [] (by simpa using hu)
    simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hh
    rcases hh with hh | hh
    · left
      simp [seq, toVal, atInstr, hh]
    · right
      simp [seq, toVal, atInstr, hh]
  case frame s f s' n fi fi' es es' h ih =>
    simp only [List.singleton_append, seqUnique, toVal, atUnique] at hu
    have hh := ih [] [] (by simpa using hu)
    simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hh
    rcases hh with hh | hh
    · left
      simp [seq, toVal, atInstr, hh]
    · right
      simp [seq, toVal, atInstr, hh]
  case br s f n cont l vs L hlen =>
    obtain ⟨extra, hb⟩ := seq_block_br s f vs L 0 [] []
    simp only [Nat.add_zero, List.append_nil] at hb
    left
    simp only [List.singleton_append, seq, toVal, atInstr, hb]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, List.reverse_reverse]
    simp [List.append_assoc]
  case return_ s f n fi k vs L hlen =>
    obtain ⟨extra, hb⟩ := seq_block_ret s fi vs L [] []
    simp only [List.append_nil] at hb
    left
    simp only [List.singleton_append, seq, toVal, atInstr, hb]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, List.reverse_reverse]
    simp [List.append_assoc]
  case callIndirect s f x y a i ht =>
    have hb := callTarget_eq_some.mpr ht
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp [toVal, atInstr, instrStep, hb]
  case callIndirectTrap s f x y i hn =>
    have hb : callTarget s f x y i = none := by
      cases he : callTarget s f x y i with
      | none => rfl
      | some a => exact False.elim (hn a (callTarget_eq_some.mp he))
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp [toVal, atInstr, instrStep, hb]
  case tableCopyTrap s f x y tx ty d src n htx hty hb =>
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    cases hx : s.tables[tx]? <;> cases hy : s.tables[ty]? <;>
      simp_all [toVal, atInstr, instrStep, tableAt, Bool.cond_eq_ite, Nat.blt_eq]
  case tableInitTrap s f x y tx ey d src n htx hey hb =>
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    cases hx : s.tables[tx]? <;> cases hy : s.elems[ey]? <;>
      simp_all [toVal, atInstr, instrStep, tableAt, Bool.cond_eq_ite, Nat.blt_eq]
  case memoryInitTrap s f x a da mem d src n hma hda hm hb =>
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    cases hd : s.datas[da]? <;>
      simp_all [toVal, atInstr, instrStep, mem0, Bool.cond_eq_ite, Nat.blt_eq]

theorem step_complete {H : HostSem} {c c₁ c₂ : Config} (h₁ : Step H c c₁) (h₂ : step c = some c₂)
    (hu : uniqueStep c = true) : c₁ = c₂ := by
  have hc := seq_complete h₁ [] [] (by simpa only [uniqueStep, List.append_nil] using hu)
  simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hc
  unfold step at h₂
  rcases hc with hs | hs
  · rw [hs] at h₂
    exact Option.some.inj h₂
  · rw [hs] at h₂
    contradiction

theorem must_of_step {H : HostSem} {Q : Outcome → Prop} {c c' : Config} (h : step c = some c')
    (hu : uniqueStep c = true) (hc' : Must H Q c') : Must H Q c := by
  refine Must.next ⟨c', step_sound h⟩ ?_
  intro c₁ hs
  have he := step_complete hs h hu
  subst c₁
  exact hc'

mutual
/-- Number of administrative nodes; instruction payloads and frames carry no weight. -/
def seqSize : List AInstr → Nat
  | [] => 0
  | e :: es => adminSize e + seqSize es

/-- One administrative node plus the nodes under a label or frame. -/
def adminSize : AInstr → Nat
  | .label _ _ body | .frame _ _ body => 1 + seqSize body
  | _ => 1
end

theorem adminSize_pos (e : AInstr) : 0 < adminSize e := by
  cases e <;> simp [adminSize]

theorem seqSize_zero (es : List AInstr) : seqSize es = 0 ↔ es = [] := by
  cases es with
  | nil => simp [seqSize]
  | cons e es =>
    have hp := adminSize_pos e
    simp only [seqSize, List.cons_ne_nil, iff_false]
    omega

theorem seqSize_append (es fs : List AInstr) :
    seqSize (es ++ fs) = seqSize es + seqSize fs := by
  induction es with
  | nil => simp [seqSize]
  | cons e es ih => simp [seqSize, ih, Nat.add_assoc]

theorem adminSize_val (v : Val) : adminSize v.instr = 1 := by
  cases v <;> try rfl
  case ref r => cases r <;> rfl

theorem seqSize_vals (vs : List Val) : seqSize (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, seqSize, adminSize_val, ih, List.length_cons]
    omega

@[simp] theorem seqTraps_values (vs : List Val) : seqTraps (vals vs) = false := by
  simpa only [List.append_nil, seqTraps] using seqTraps_vals vs []

theorem seqTraps_blockPlain (args : List Val) {i : Instr} (hi : toVal (.plain i) = none)
    {l : Nat} (L : BlockCtx l) :
    ∀ rest, seqTraps (L.fill (vals args ++ [.plain i]) ++ rest) = false := by
  induction L with
  | base vs tail =>
    intro rest
    simp only [BlockCtx.fill, List.append_assoc, seqTraps_vals, List.cons_append,
      seqTraps, hi, atTrap]
  | label vs n cont inner tail ih =>
    intro rest
    simp only [BlockCtx.fill, List.append_assoc, seqTraps_vals, List.cons_append,
      seqTraps, toVal, atTrap]
    simpa only [List.append_nil] using ih []

theorem seqTraps_eval (E : EvalCtx) :
    ∀ rest, seqTraps (E.fill [.trap] ++ rest) = true := by
  induction E with
  | hole => intro rest; rfl
  | seq vs inner tail ih =>
    intro rest
    simp only [EvalCtx.fill, List.append_assoc, seqTraps_vals]
    exact ih _
  | label n cont inner ih =>
    intro rest
    simp only [EvalCtx.fill, List.cons_append, List.nil_append, seqTraps, toVal, atTrap]
    simpa only [List.append_nil] using ih []

theorem seqSize_eval_pos (E : EvalCtx) : 0 < seqSize (E.fill [.trap]) := by
  induction E with
  | hole => decide
  | seq vs inner tail ih =>
    simp only [EvalCtx.fill, seqSize_append]
    omega
  | label n cont inner ih => simp [EvalCtx.fill, seqSize, adminSize]

theorem seqSize_eval_trap (E : EvalCtx) (hne : E.fill [.trap] ≠ [.trap]) :
    seqSize [.trap] < seqSize (E.fill [.trap]) := by
  induction E with
  | hole => exact (hne rfl).elim
  | seq vs inner tail ih =>
    by_cases he : inner.fill [.trap] = [.trap]
    · have hz : 0 < vs.length + seqSize tail := by
        by_contra hn
        have hv : vs = [] := List.length_eq_zero_iff.mp (by omega)
        have ht : tail = [] := (seqSize_zero tail).mp (by omega)
        exact hne (by simp [EvalCtx.fill, he, hv, ht])
      simp only [EvalCtx.fill, seqSize_append, seqSize_vals, he, seqSize, adminSize]
      omega
    · have hh := ih he
      simp only [EvalCtx.fill, seqSize_append]
      omega
  | label n cont inner ih =>
    have hp := seqSize_eval_pos inner
    simp only [EvalCtx.fill, seqSize, adminSize]
    omega

set_option maxHeartbeats 1000000 in
theorem step_traps {H : HostSem} {c c' : Config} (h : Step H c c') :
    ∀ rest, seqTraps (c.instrs ++ rest) = true →
      c'.store = c.store ∧ c'.frame = c.frame ∧
      seqTraps (c'.instrs ++ rest) = true ∧ seqSize c'.instrs < seqSize c.instrs := by
  induction h
  all_goals intro rest ht
  all_goals dsimp only at *
  case num s f i args r hr =>
    have hn := num_toVal_none hr
    simp only [List.append_assoc, seqTraps_vals, List.cons_append, List.nil_append,
      seqTraps, hn, atTrap] at ht
    contradiction
  case seq s f s' f' es es' vs tail h ih =>
    simp only [List.append_assoc, seqTraps_vals] at ht
    obtain ⟨hs, hf, hh, hsize⟩ := ih (tail ++ rest) ht
    refine ⟨hs, hf, ?_, ?_⟩
    · simpa only [List.append_assoc, seqTraps_vals] using hh
    · simp only [seqSize_append]
      omega
  case label s f s' f' n cont es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    obtain ⟨hs, hf, hh, hsize⟩ := ih [] (by simpa using ht)
    refine ⟨hs, hf, ?_, ?_⟩
    · simpa only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap,
        List.append_nil] using hh
    · simp only [seqSize, adminSize]
      omega
  case frame s f s' n fi fi' es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    obtain ⟨hs, hf, hh, hsize⟩ := ih [] (by simpa using ht)
    refine ⟨hs, rfl, ?_, ?_⟩
    · simpa only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap,
        List.append_nil] using hh
    · simp only [seqSize, adminSize]
      omega
  case trap s f E hne => exact ⟨rfl, rfl, rfl, seqSize_eval_trap E hne⟩
  case trapFrame => exact ⟨rfl, rfl, rfl, by simp [seqSize, adminSize]⟩
  case br s f n cont l vs L hlen =>
    have hh := seqTraps_blockPlain vs (i := .br l) rfl L []
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    simp only [List.append_nil] at hh
    rw [hh] at ht
    contradiction
  case return_ s f n fi k vs L hlen =>
    have hh := seqTraps_blockPlain vs (i := .return_) rfl L []
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    simp only [List.append_nil] at hh
    rw [hh] at ht
    contradiction
  all_goals
    simp only [List.append_assoc, seqTraps_vals, List.cons_append, List.nil_append,
      seqTraps, toVal_instr] at ht
    simp [toVal, atTrap, seqTraps_values] at ht

theorem seqTraps_final {s f stk es} (ht : seqTraps es = true)
    (hf : seq s f stk es = .final) : stk = [] ∧ es = [.trap] := by
  rcases seq_final hf with hh | ⟨vs, hv⟩
  · exact hh
  · have hh := congrArg seqTraps hv
    rw [seqTraps_vals, seqTraps_values, ht] at hh
    contradiction

theorem seqTraps_runs (s : Store) (f : Frame) (stk : List Val) (es : List AInstr)
    (ht : seqTraps es = true) :
    seq s f stk es = .final ∨ ∃ s' f' es', seq s f stk es = .step s' f' es' := by
  cases es with
  | nil => contradiction
  | cons e rest =>
    cases hv : toVal e with
    | some v =>
      have ht' : seqTraps rest = true := by simpa only [seqTraps, hv] using ht
      simpa only [seq, hv] using seqTraps_runs s f (v :: stk) rest ht'
    | none =>
      simp only [seqTraps, hv] at ht
      simp only [seq, hv]
      cases e with
      | trap =>
        simp only [atInstr, Bool.cond_eq_ite]
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨s, f, [.trap], rfl⟩
      | label n cont body =>
        have ht' : seqTraps body = true := ht
        rcases seqTraps_runs s f [] body ht' with hf | ⟨s', f', body', hs⟩
        · have hb := (seqTraps_final ht' hf).2
          subst body
          exact Or.inr ⟨s, f, vals stk.reverse ++ [.trap] ++ rest, rfl⟩
        · right
          exact ⟨s', f', vals stk.reverse ++ [.label n cont body'] ++ rest,
            by simp only [atInstr, hs]⟩
      | frame n fi body =>
        have ht' : seqTraps body = true := ht
        rcases seqTraps_runs s fi [] body ht' with hf | ⟨s', fi', body', hs⟩
        · have hb := (seqTraps_final ht' hf).2
          subst body
          exact Or.inr ⟨s, f, vals stk.reverse ++ [.trap] ++ rest, rfl⟩
        · right
          exact ⟨s', f, vals stk.reverse ++ [.frame n fi' body'] ++ rest,
            by simp only [atInstr, hs]⟩
      | _ => contradiction
termination_by sizeOf es

theorem must_trap {H : HostSem} {Q : Outcome → Prop} {c : Config}
    (ht : seqTraps c.instrs = true) (hQ : Q (.trapped c.store)) : Must H Q c := by
  by_cases hf : c.instrs = [.trap]
  · exact Must.done (o := .trapped c.store) ⟨rfl, hf⟩ hQ
  · have hs : ∃ c', Step H c c' := by
      rcases seqTraps_runs c.store c.frame [] c.instrs ht with hh | ⟨s', f', es', hh⟩
      · exact False.elim (hf (seqTraps_final ht hh).2)
      · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := H) hh⟩
    refine Must.next hs ?_
    intro c' hstep
    obtain ⟨hstore, hframe, htrap, hsize⟩ := step_traps hstep [] (by simpa using ht)
    exact must_trap (by simpa using htrap) (by simpa only [hstore] using hQ)
termination_by seqSize c.instrs

theorem runDet_must {H : HostSem} {Q : Outcome → Prop} {n : Nat} {c c' : Config}
    (h : runDet n c = some c') (hQ : ∀ o, Final c' o → Q o) : Must H Q c := by
  induction n generalizing c with
  | zero => simp only [runDet, reduceCtorEq] at h
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true] at h
      have he := Option.some.inj h
      subst c'
      exact must_trap ht (hQ (.trapped c.store) ⟨rfl, rfl⟩)
    | false =>
      simp only [runDet, ht, Bool.cond_false] at h
      cases hu : uniqueStep c with
      | false => simp only [hu, Bool.cond_false, reduceCtorEq] at h
      | true =>
        simp only [hu, Bool.cond_true] at h
        cases hs : seq c.store c.frame [] c.instrs with
        | step s f es =>
          simp only [hs] at h
          exact must_of_step (by simp only [step, hs]) hu (ih h)
        | final =>
          simp only [hs] at h
          have he := Option.some.inj h
          subst c'
          rcases seq_final hs with ⟨_, htrap⟩ | ⟨vs, hvals⟩
          · have hf : Final c (.trapped c.store) := ⟨rfl, htrap⟩
            exact Must.done hf (hQ _ hf)
          · have hf : Final c (.returned c.store vs) := ⟨rfl, by simpa using hvals⟩
            exact Must.done hf (hQ _ hf)
        | _ => simp only [hs, reduceCtorEq] at h

end FVA.Wasm.Exec.Ref
