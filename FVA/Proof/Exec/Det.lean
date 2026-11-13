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

theorem seqUnique_vals (fits : Bool) (s : Store) (f : Frame) (vs ws : List Val)
    (es : List AInstr) :
    seqUnique fits s f vs (vals ws ++ es) = seqUnique fits s f (ws.reverse ++ vs) es := by
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
    {fits : Bool} (s : Store) (f : Frame) (stk : List Val) (hr : r ∈ numResults i args)
    (hu : instrUnique fits i (args.reverse ++ stk) = true) :
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

theorem atUnique_plain {fits : Bool} {s : Store} {f : Frame} {vs : List Val} {i : Instr}
    {rest : List AInstr} (h : i ≠ .throwRef) :
    atUnique fits s f vs (.plain i) rest = instrUnique fits i vs := by
  cases i <;> first | rfl | exact absurd rfl h

theorem seqUnique_eval_trap (fits : Bool) (s : Store) (f : Frame) (E : EvalCtx) :
    ∀ (stk : List Val) (rest : List AInstr),
      seqUnique fits s f stk (E.fill [.trap] ++ rest) = false := by
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
  | handler n cs inner ih =>
    intro stk rest
    simp only [EvalCtx.fill, List.singleton_append, seqUnique, toVal, atUnique]
    simpa only [List.append_nil] using ih [] []

/-- A clause that does not take the exception is one the stepper skips. -/
theorem catchStep_eq_none {s : Store} {f : Frame} {a : Nat} {c : Catch}
    (h : ¬ c.Catches s f a) : catchStep s f a c = none := by
  cases c with
  | tag x l | tagRef x l =>
    simp only [catchStep]
    split
    · rename_i e ta he hta
      cases hb : (ta == e.tag)
      · rfl
      · exact absurd ⟨e, he, by rw [hta, beq_iff_eq.mp hb]⟩ h
    · rfl
  | all l | allRef l => exact absurd trivial h

/-- The stepper's tail call out of a block context: the arguments, for the frame to invoke. -/
theorem seq_block_retInvoke (s : Store) (f : Frame) (args : List Val) {a : Nat} {fn : FuncInst}
    {ft : FuncType} (hfn : s.funcs[a]? = some fn) (hft : fn.type.expand = some ft)
    (hlen : args.length = ft.params.length) {l : Nat} (L : BlockCtx l) :
    ∀ (stk : List Val) (rest : List AInstr),
      seq s f stk (L.fill (vals args ++ [.returnInvoke a]) ++ rest) = .retInvoke a args := by
  induction L with
  | base vs tail =>
    intro stk rest
    simp only [BlockCtx.fill, List.append_assoc, seq_vals, List.cons_append, seq, toVal,
      atInstr, hfn, hft]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append, List.length_reverse,
      stack_take, List.reverse_reverse]
    simp
  | label vs n cont inner tail ih =>
    intro stk rest
    simp only [BlockCtx.fill, List.append_assoc, seq_vals, List.cons_append, seq, toVal,
      atInstr]
    have hx := ih [] []
    simp only [List.append_nil] at hx
    simp only [hx]
  | handler vs n cs inner tail ih =>
    intro stk rest
    simp only [BlockCtx.fill, List.append_assoc, seq_vals, List.cons_append, seq, toVal,
      atInstr]
    have hx := ih [] []
    simp only [List.append_nil] at hx
    simp only [hx]

set_option maxHeartbeats 1000000 in
theorem seq_complete {H : HostSem} {fits : Bool} {c c' : Config} (h : StepP H fits c c') :
    ∀ (stk : List Val) (rest : List AInstr),
      seqUnique fits c.store c.frame stk (c.instrs ++ rest) = true →
      seq c.store c.frame stk (c.instrs ++ rest) =
          .step c'.store c'.frame (vals stk.reverse ++ c'.instrs ++ rest) ∨
        seq c.store c.frame stk (c.instrs ++ rest) = .stuck := by
  induction h
  all_goals intro stk rest hu
  case num s f i args r hr =>
    have hn := num_toVal_none hr
    have hi : i ≠ .throwRef := by rintro rfl; simp [numResults] at hr
    simp only [List.append_assoc, seqUnique_vals, List.singleton_append, seqUnique,
      hn, atUnique_plain hi] at hu
    left
    rw [List.append_assoc, seq_vals]
    simp only [List.singleton_append, seq, hn]
    exact atInstr_plain_of_step rest (num_instr_complete s f stk hr hu)
  case refNull | refIsNull | refFunc | drop | select | localGet | localSet | localTee | globalGet |
      globalSet | tableGet | tableGetTrap | tableSet | tableSetTrap | tableSize | elemDrop |
      load | loadTrap | loadPacked | loadPackedTrap | store | storeTrap | storePacked |
      storePackedTrap | memorySize | dataDrop | nop | unreachable | ifTrue | ifFalse |
      brIfTrue | brIfFalse | brTable | call | returnCall | returnCallRef | returnCallRefNull |
      callRef | callRefNull =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, tableAt, mem0, Bool.cond_eq_ite, Nat.blt_eq]
    all_goals split_ifs <;> first | omega | simp_all
  case refAsNonNullNull | brOnNull | brOnNonNullNull | throwRefNull =>
    left
    simp [seq, toVal, atInstr, instrStep, Ref.isNull]
  case tableFillTrap | tableFillZero | tableFill | tableCopyZero | tableCopyUp | tableCopyDown |
      tableInitZero | tableInit | memoryFillTrap | memoryFillZero | memoryFill |
      memoryCopyTrap | memoryCopyZero | memoryCopyUp | memoryCopyDown |
      memoryInitZero | memoryInit =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, tableAt, mem0, Bool.cond_eq_ite, Nat.blt_eq,
      Nat.beq_eq, Nat.ble_eq]
    all_goals split_ifs <;> first | omega | simp_all
  case memoryGrow s f a mem mem' n hma hm hg =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, mem0]
  case memoryGrowFail s f n hfail =>
    simp only [List.cons_append, List.nil_append, seqUnique, toVal_instr, atUnique,
      instrUnique] at hu
    have hno := hfail hu
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    cases hma : f.inst.mems[0]? with
    | none => right; simp_all [toVal, atInstr, instrStep, mem0]
    | some a =>
      cases hm : s.mems[a]? with
      | none => right; simp_all [toVal, atInstr, instrStep, mem0]
      | some mem => left; simp_all [toVal, atInstr, instrStep, mem0, hno a mem hma hm]
  case tableGrow s f x ta t t' r n hta ht hg =>
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp_all [toVal, atInstr, instrStep, tableAt]
  case tableGrowFail s f x r n hfail =>
    simp only [List.cons_append, List.nil_append, seqUnique, toVal_instr, atUnique,
      instrUnique] at hu
    have hno := hfail hu
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    cases hta : f.inst.tables[x]? with
    | none => right; simp_all [toVal, atInstr, instrStep, tableAt]
    | some ta =>
      cases ht : s.tables[ta]? with
      | none => right; simp_all [toVal, atInstr, instrStep, tableAt]
      | some t => left; simp_all [toVal, atInstr, instrStep, tableAt, hno ta t hta ht]
  case invokeHost | invokeHostTrap | invokeHostDiverge | trapFrame =>
    simp only [List.append_assoc, seqUnique_vals, List.cons_append, List.nil_append,
      seqUnique] at hu
    simp_all [toVal, seqUnique, atUnique]
  case trap s f E hne =>
    have ht := seqUnique_eval_trap fits s f E stk rest
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
  case invoke s f a dt ft inst code vs hf hft hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr, hf, hft]
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
  case refAsNonNull s f r hr | brOnNullValue s f l r hr | brOnNonNull s f l r hr =>
    left
    cases r with
    | null => exact absurd rfl hr
    | _ => simp [seq, toVal, atInstr, instrStep, Ref.isNull, Val.instr]
  case returnCallIndirect s f x y a i ht =>
    have hb := callTarget_eq_some.mpr ht
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp [toVal, atInstr, instrStep, hb]
  case returnCallIndirectTrap s f x y i hn =>
    have hb : callTarget s f x y i = none := by
      cases he : callTarget s f x y i with
      | none => rfl
      | some a => exact False.elim (hn a (callTarget_eq_some.mp he))
    left
    simp only [List.cons_append, List.nil_append, seq, toVal_instr]
    simp [toVal, atInstr, instrStep, hb]
  case handler s f s' f' n cs es es' h ih =>
    simp only [List.singleton_append, seqUnique, toVal, atUnique] at hu
    have hh := ih [] [] (by simpa using hu)
    simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hh
    rcases hh with hh | hh
    · left
      simp [seq, toVal, atInstr, hh]
    · right
      simp [seq, toVal, atInstr, hh]
  case tryTable s f bt cs body ft vs hft hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr,
      instrStep, hft, Option.bind_some]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, stack_drop, List.reverse_reverse]
    simp
  case throw s f x ta ti ft vs hta hti hft hres hlen =>
    left
    simp only [List.append_assoc, seq_vals, List.singleton_append, seq, toVal, atInstr,
      instrStep, hta, hti, hft, Option.bind_some, hres, List.isEmpty_nil, Bool.not_true,
      Bool.false_or]
    simp only [← hlen, Bool.cond_eq_ite, Nat.blt_eq, List.length_append,
      List.length_reverse, stack_take, stack_drop, List.reverse_reverse]
    simp
  case handlerExit =>
    left
    simp [seq, toVal, atInstr, seq_values, isTrapOnly_vals, List.append_assoc]
  case throwRefInstrs s f a vs tail hne =>
    simp only [throwing, List.append_assoc, seqUnique_vals, List.cons_append, List.nil_append,
      seqUnique, toVal, atUnique, Bool.and_eq_true, List.isEmpty_iff,
      List.append_eq_nil_iff, List.reverse_eq_nil_iff] at hu
    rcases hne with hv | ht <;> simp_all
  case throwRefLabel | throwRefFrame | throwRefHandlerEmpty =>
    left
    simp [seq, toVal, atInstr, throwing]
  case throwRefCatch s f a n x l cs e he hx | throwRefCatchRef s f a n x l cs e he hx =>
    left
    simp [seq, toVal, atInstr, throwing, catchStep, he, hx]
  case throwRefCatchAll | throwRefCatchAllRef =>
    left
    simp [seq, toVal, atInstr, throwing, catchStep]
  case throwRefHandlerNext s f a n c cs hn =>
    left
    simp [seq, toVal, atInstr, throwing, catchStep_eq_none hn]
  case returnInvoke s f n fi k a fn ft vs L hfn hft hlen =>
    have hb := seq_block_retInvoke s fi vs hfn hft hlen L [] []
    simp only [List.append_nil] at hb
    left
    simp only [List.singleton_append, seq, toVal, atInstr, hb]
    simp [List.append_assoc]
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

theorem step_complete {H : HostSem} {fits : Bool} {c c₁ c₂ : Config} (h₁ : StepP H fits c c₁)
    (h₂ : step c = some c₂) (hu : uniqueStep fits c = true) : c₁ = c₂ := by
  have hc := seq_complete h₁ [] [] (by simpa only [uniqueStep, List.append_nil] using hu)
  simp only [List.append_nil, List.reverse_nil, vals, List.map_nil, List.nil_append] at hc
  unfold step at h₂
  rcases hc with hs | hs
  · rw [hs] at h₂
    exact Option.some.inj h₂
  · rw [hs] at h₂
    contradiction

theorem must_of_step {H : HostSem} {Q : Outcome → Prop} {c c' : Config} (h : step c = some c')
    (hu : uniqueStep false c = true) (hc' : Must H Q c') : Must H Q c := by
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
  | .label _ _ body | .frame _ _ body | .handler _ _ body => 1 + seqSize body
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

theorem seqTraps_blockAtom (args : List Val) {e : AInstr} (hv : toVal e = none)
    (ht : atTrap e = false) {l : Nat} (L : BlockCtx l) :
    ∀ rest, seqTraps (L.fill (vals args ++ [e]) ++ rest) = false := by
  induction L with
  | base vs tail =>
    intro rest
    simp only [BlockCtx.fill, List.append_assoc, seqTraps_vals, List.cons_append,
      seqTraps, hv, ht]
  | label vs n cont inner tail ih =>
    intro rest
    simp only [BlockCtx.fill, List.append_assoc, seqTraps_vals, List.cons_append,
      seqTraps, toVal, atTrap]
    simpa only [List.append_nil] using ih []
  | handler vs n cs inner tail ih =>
    intro rest
    simp only [BlockCtx.fill, List.append_assoc, seqTraps_vals, List.cons_append,
      seqTraps, toVal, atTrap]
    simpa only [List.append_nil] using ih []

theorem seqTraps_blockPlain (args : List Val) {i : Instr} (hi : toVal (.plain i) = none)
    {l : Nat} (L : BlockCtx l) :
    ∀ rest, seqTraps (L.fill (vals args ++ [.plain i]) ++ rest) = false :=
  seqTraps_blockAtom args hi rfl L

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
  | handler n cs inner ih =>
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
  | handler n cs inner ih => simp [EvalCtx.fill, seqSize, adminSize]

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
  | handler n cs inner ih =>
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
  case handler s f s' f' n cs es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    obtain ⟨hs, hf, hh, hsize⟩ := ih [] (by simpa using ht)
    refine ⟨hs, hf, ?_, ?_⟩
    · simpa only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap,
        List.append_nil] using hh
    · simp only [seqSize, adminSize]
      omega
  case returnInvoke s f n fi k a fn ft vs L hfn hft hlen =>
    have hh := seqTraps_blockAtom vs (e := .returnInvoke a) rfl rfl L []
    simp only [List.cons_append, List.nil_append, seqTraps, toVal, atTrap] at ht
    simp only [List.append_nil] at hh
    rw [hh] at ht
    contradiction
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
      seqTraps, toVal_instr, throwing] at ht
    simp [toVal, atTrap, seqTraps_values, seqTraps] at ht

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
      | handler n cs body =>
        have ht' : seqTraps body = true := ht
        rcases seqTraps_runs s f [] body ht' with hf | ⟨s', f', body', hs⟩
        · have hb := (seqTraps_final ht' hf).2
          subst body
          exact Or.inr ⟨s, f, vals stk.reverse ++ [.trap] ++ rest, rfl⟩
        · right
          exact ⟨s', f', vals stk.reverse ++ [.handler n cs body'] ++ rest,
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

/-! ## Exception propagation (contract T4)

A pending throw's administrative steps keep the store and the frame and end at the same place:
the nearest enclosing handler, holding exactly the thrown exception (`seqThrow … = some (.inr L)`:
every execution passes through `L`), or the top (`.inl a`: every execution ends `throwing a`). -/

theorem seqThrow_vals (stk vs : List Val) (es : List AInstr) :
    seqThrow stk (vals vs ++ es) = seqThrow (vs.reverse ++ stk) es := by
  induction vs generalizing stk with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals, List.map_cons, List.cons_append, seqThrow, toVal_instr]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

@[simp] theorem seqThrow_values (stk vs : List Val) : seqThrow stk (vals vs) = none := by
  simpa only [List.append_nil, seqThrow] using seqThrow_vals stk vs []

theorem seqThrow_throwing (stk : List Val) (a : Nat) (rest : List AInstr) :
    seqThrow stk (throwing a ++ rest) = some (.inl a) := rfl

@[simp] theorem seqThrow_throwing' (stk : List Val) (a : Nat) :
    seqThrow stk (throwing a) = some (.inl a) := rfl

theorem isThrowing_eq_true {es : List AInstr} : isThrowing es = true ↔ ∃ a, es = throwing a := by
  constructor
  · intro h
    fun_cases isThrowing es
    · exact ⟨_, rfl⟩
    · simp_all [isThrowing]
  · rintro ⟨a, rfl⟩
    rfl

theorem seqThrow_blockAtom (args : List Val) {e : AInstr} (hv : toVal e = none)
    (ht : ∀ stk rest, atThrow stk e rest = none) {l : Nat} (L : BlockCtx l) :
    ∀ stk rest, seqThrow stk (L.fill (vals args ++ [e]) ++ rest) = none := by
  induction L with
  | base vs tail =>
    intro stk rest
    simp only [BlockCtx.fill, List.append_assoc, seqThrow_vals, List.cons_append, seqThrow, hv,
      ht]
  | label vs n cont inner tail ih =>
    intro stk rest
    have hi := ih [] []
    simp only [List.append_nil] at hi
    simp only [BlockCtx.fill, List.append_assoc, seqThrow_vals, List.cons_append, seqThrow,
      toVal, atThrow, hi]
  | handler vs n cs inner tail ih =>
    intro stk rest
    have hi := ih [] []
    simp only [List.append_nil] at hi
    simp only [BlockCtx.fill, List.append_assoc, seqThrow_vals, List.cons_append, seqThrow,
      toVal, atThrow, hi]

theorem seqThrow_eval_trap (E : EvalCtx) :
    ∀ stk rest, seqThrow stk (E.fill [.trap] ++ rest) = none := by
  induction E with
  | hole => intro stk rest; rfl
  | seq vs inner tail ih =>
    intro stk rest
    simp only [EvalCtx.fill, List.append_assoc, seqThrow_vals]
    exact ih _ _
  | label n cont inner ih =>
    intro stk rest
    have hi := ih [] []
    simp only [List.append_nil] at hi
    simp only [EvalCtx.fill, List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hi]
  | handler n cs inner ih =>
    intro stk rest
    have hi := ih [] []
    simp only [List.append_nil] at hi
    simp only [EvalCtx.fill, List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hi]

theorem seqSize_throwing (a : Nat) : seqSize (throwing a) = 2 := rfl

set_option maxHeartbeats 2000000 in
/-- Every step from a configuration with a pending throw is one of its administrative steps. -/
theorem step_throw {H : HostSem} {c c' : Config} (h : Step H c c') :
    ∀ stk rest r, seqThrow stk (c.instrs ++ rest) = some r →
      c'.store = c.store ∧ c'.frame = c.frame ∧ seqSize c'.instrs < seqSize c.instrs ∧
      (seqThrow stk (c'.instrs ++ rest) = some r ∨
        ∃ L, r = .inr L ∧ vals stk.reverse ++ c'.instrs ++ rest = L) := by
  induction h
  all_goals intro stk rest r ht
  all_goals dsimp only at *
  case seq s f s' f' es es' vs tail h ih =>
    simp only [List.append_assoc, seqThrow_vals] at ht
    obtain ⟨hs, hf, hsize, hh⟩ := ih (vs.reverse ++ stk) (tail ++ rest) r ht
    refine ⟨hs, hf, ?_, ?_⟩
    · simp only [seqSize_append]
      omega
    · rcases hh with hh | ⟨L, rfl, hl⟩
      · exact Or.inl (by simpa only [List.append_assoc, seqThrow_vals] using hh)
      · refine Or.inr ⟨L, rfl, ?_⟩
        rw [← hl]
        simp only [List.reverse_append, List.reverse_reverse, List.map_append, List.append_assoc]
  case label s f s' f' n cont es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow] at ht
    split at ht <;> try contradiction
    · rename_i a hb
      cases ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inl a) (by simpa using hb)
      refine ⟨hs, hf, by simp only [seqSize, adminSize]; omega, Or.inl ?_⟩
      rcases hh with hh | ⟨L, hL, -⟩
      · simp only [List.append_nil] at hh
        simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hh]
      · cases hL
    · rename_i body' hb
      cases ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inr body') (by simpa using hb)
      refine ⟨hs, hf, by simp only [seqSize, adminSize]; omega, ?_⟩
      rcases hh with hh | ⟨L, hL, hl⟩
      · simp only [List.append_nil] at hh
        exact Or.inl (by simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow,
          hh])
      · cases hL
        simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl
        subst hl
        exact Or.inr ⟨_, rfl, by simp⟩
  case frame s f s' n fi fi' es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow] at ht
    split at ht <;> try contradiction
    · rename_i a hb
      cases ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inl a) (by simpa using hb)
      subst hf
      refine ⟨hs, rfl, by simp only [seqSize, adminSize]; omega, Or.inl ?_⟩
      rcases hh with hh | ⟨L, hL, -⟩
      · simp only [List.append_nil] at hh
        simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hh]
      · cases hL
    · rename_i body' hb
      cases ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inr body') (by simpa using hb)
      subst hf
      refine ⟨hs, rfl, by simp only [seqSize, adminSize]; omega, ?_⟩
      rcases hh with hh | ⟨L, hL, hl⟩
      · simp only [List.append_nil] at hh
        exact Or.inl (by simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow,
          hh])
      · cases hL
        simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl
        subst hl
        exact Or.inr ⟨_, rfl, by simp⟩
  case handler s f s' f' n cs es es' h ih =>
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow] at ht
    split at ht <;> try contradiction
    · rename_i a hb
      cases hth : isThrowing es <;> simp only [hth, Bool.cond_true, Bool.cond_false,
        reduceCtorEq, Option.some.injEq] at ht
      subst ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inl a) (by simpa using hb)
      refine ⟨hs, hf, by simp only [seqSize, adminSize]; omega, ?_⟩
      rcases hh with hh | ⟨L, hL, -⟩
      · simp only [List.append_nil] at hh
        cases hth' : isThrowing es'
        · exact Or.inl (by simp only [List.cons_append, List.nil_append, seqThrow, toVal,
            atThrow, hh, hth', Bool.cond_false])
        · obtain ⟨a', rfl⟩ := isThrowing_eq_true.mp hth'
          have ha : a' = a := by
            rw [seqThrow_throwing'] at hh
            exact Sum.inl.inj (Option.some.inj hh)
          subst ha
          exact Or.inr ⟨_, rfl, by simp⟩
      · cases hL
    · rename_i body' hb
      cases ht
      obtain ⟨hs, hf, hsize, hh⟩ := ih [] [] (.inr body') (by simpa using hb)
      refine ⟨hs, hf, by simp only [seqSize, adminSize]; omega, ?_⟩
      rcases hh with hh | ⟨L, hL, hl⟩
      · simp only [List.append_nil] at hh
        exact Or.inl (by simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow,
          hh])
      · cases hL
        simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl
        subst hl
        exact Or.inr ⟨_, rfl, by simp⟩
  case throwRefInstrs s f a vs tail hne =>
    simp only [List.append_assoc, seqThrow_vals, seqThrow_throwing] at ht
    cases ht
    refine ⟨rfl, rfl, ?_, Or.inl (seqThrow_throwing _ _ _)⟩
    simp only [seqSize_append, seqSize_vals, seqSize_throwing]
    rcases hne with hv | ht
    · have := List.length_pos_iff.mpr hv
      omega
    · have := (seqSize_zero tail).not.mpr ht
      omega
  case throwRefLabel s f a n cont | throwRefFrame s f a n fi =>
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow] at ht
    cases ht
    exact ⟨rfl, rfl, by simp [seqSize, adminSize], Or.inl (seqThrow_throwing _ _ _)⟩
  case trap s f E hne =>
    rw [seqThrow_eval_trap] at ht
    contradiction
  case br s f n cont l vs L hlen =>
    have hh := seqThrow_blockAtom vs (e := .plain (.br l)) rfl (fun _ _ => rfl) L [] []
    simp only [List.append_nil] at hh
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hh,
      reduceCtorEq] at ht
  case return_ s f n fi k vs L hlen =>
    have hh := seqThrow_blockAtom vs (e := .plain .return_) rfl (fun _ _ => rfl) L [] []
    simp only [List.append_nil] at hh
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hh,
      reduceCtorEq] at ht
  case returnInvoke s f n fi k a fn ft vs L hfn hft hlen =>
    have hh := seqThrow_blockAtom vs (e := .returnInvoke a) rfl (fun _ _ => rfl) L [] []
    simp only [List.append_nil] at hh
    simp only [List.cons_append, List.nil_append, seqThrow, toVal, atThrow, hh,
      reduceCtorEq] at ht
  case num s f i args r' hr =>
    have hn := num_toVal_none hr
    have hi : i ≠ .throwRef := by rintro rfl; simp [numResults] at hr
    simp only [List.append_assoc, seqThrow_vals, List.cons_append, seqThrow, hn] at ht
    cases i <;> simp_all [atThrow]
  all_goals
    simp only [List.append_assoc, seqThrow_vals, List.cons_append, List.nil_append,
      seqThrow, toVal_instr, throwing] at ht
    simp [toVal, atThrow, seqThrow_values, seqThrow, isThrowing, throwing] at ht

theorem seqThrow_runs (s : Store) (f : Frame) (stk : List Val) (es : List AInstr)
    (r : Nat ⊕ List AInstr) (ht : seqThrow stk es = some r) :
    (∃ a, r = .inl a ∧ seq s f stk es = .thrown a) ∨
      ∃ s' f' es', seq s f stk es = .step s' f' es' := by
  cases es with
  | nil => simp [seqThrow] at ht
  | cons e rest =>
    cases hv : toVal e with
    | some v =>
      have ht' : seqThrow (v :: stk) rest = some r := by simpa only [seqThrow, hv] using ht
      simpa only [seq, hv] using seqThrow_runs s f (v :: stk) rest r ht'
    | none =>
      simp only [seqThrow, hv] at ht
      simp only [seq, hv]
      cases e with
      | plain i =>
        cases i <;> simp only [atThrow, reduceCtorEq] at ht
        case throwRef =>
          split at ht <;> try contradiction
          rename_i a stk'
          cases ht
          simp only [atInstr]
          cases hb : (stk'.isEmpty && rest.isEmpty)
          · exact Or.inr ⟨s, f, throwing a, by simp only [Bool.cond_false]⟩
          · exact Or.inl ⟨a, rfl, by simp only [Bool.cond_true]⟩
      | label n cont body =>
        simp only [atThrow] at ht
        split at ht <;> try contradiction
        · rename_i a hb
          rcases seqThrow_runs s f [] body _ hb with ⟨a', -, hs⟩ | ⟨s', f', body', hs⟩
          · exact Or.inr ⟨s, f, vals stk.reverse ++ throwing a' ++ rest,
              by simp only [atInstr, hs]⟩
          · exact Or.inr ⟨s', f', vals stk.reverse ++ [.label n cont body'] ++ rest,
              by simp only [atInstr, hs]⟩
        · rename_i body' hb
          rcases seqThrow_runs s f [] body _ hb with ⟨a', hr, -⟩ | ⟨s', f', body'', hs⟩
          · cases hr
          · exact Or.inr ⟨s', f', vals stk.reverse ++ [.label n cont body''] ++ rest,
              by simp only [atInstr, hs]⟩
      | frame n fi body =>
        simp only [atThrow] at ht
        split at ht <;> try contradiction
        · rename_i a hb
          rcases seqThrow_runs s fi [] body _ hb with ⟨a', -, hs⟩ | ⟨s', fi', body', hs⟩
          · exact Or.inr ⟨s, f, vals stk.reverse ++ throwing a' ++ rest,
              by simp only [atInstr, hs]⟩
          · exact Or.inr ⟨s', f, vals stk.reverse ++ [.frame n fi' body'] ++ rest,
              by simp only [atInstr, hs]⟩
        · rename_i body' hb
          rcases seqThrow_runs s fi [] body _ hb with ⟨a', hr, -⟩ | ⟨s', fi', body'', hs⟩
          · cases hr
          · exact Or.inr ⟨s', f, vals stk.reverse ++ [.frame n fi' body''] ++ rest,
              by simp only [atInstr, hs]⟩
      | handler n cs body =>
        simp only [atThrow] at ht
        split at ht <;> try contradiction
        · rename_i a hb
          cases hth : isThrowing body <;> simp only [hth, Bool.cond_true, Bool.cond_false,
            reduceCtorEq] at ht
          rcases seqThrow_runs s f [] body _ hb with ⟨a', -, hs⟩ | ⟨s', f', body', hs⟩
          · have he := seq_thrown hs
            simp only [List.reverse_nil, List.map_nil, List.nil_append] at he
            subst he
            simp [isThrowing] at hth
          · exact Or.inr ⟨s', f', vals stk.reverse ++ [.handler n cs body'] ++ rest,
              by simp only [atInstr, hs]⟩
        · rename_i body' hb
          rcases seqThrow_runs s f [] body _ hb with ⟨a', hr, -⟩ | ⟨s', f', body'', hs⟩
          · cases hr
          · exact Or.inr ⟨s', f', vals stk.reverse ++ [.handler n cs body''] ++ rest,
              by simp only [atInstr, hs]⟩
      | _ => simp [atThrow] at ht
termination_by sizeOf es

/-- `must_throw`: a pending throw no handler encloses ends every execution uncaught, with the
same store. -/
theorem must_throw {H : HostSem} {Q : Outcome → Prop} {c : Config} {a : Nat}
    (ht : seqThrow [] c.instrs = some (.inl a)) (hQ : Q (.thrown c.store a)) : Must H Q c := by
  by_cases hf : c.instrs = throwing a
  · exact Must.done (o := .thrown c.store a) ⟨rfl, hf⟩ hQ
  · have hs : ∃ c', Step H c c' := by
      rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, hh⟩ |
        ⟨s', f', es', hh⟩
      · cases ha
        exact False.elim (hf (by simpa using seq_thrown hh))
      · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := H) hh⟩
    refine Must.next hs ?_
    intro c' hstep
    obtain ⟨hstore, hframe, hsize, hh⟩ := step_throw hstep [] [] _ (by simpa using ht)
    rcases hh with hh | ⟨L, hL, -⟩
    · exact must_throw (by simpa using hh) (by simpa only [hstore] using hQ)
    · cases hL
termination_by seqSize c.instrs

/-- A pending throw inside a handler reaches that handler: every execution passes through `L`. -/
theorem must_throwHandler {H : HostSem} {Q : Outcome → Prop} {c : Config} {L : List AInstr}
    (ht : seqThrow [] c.instrs = some (.inr L)) (hL : Must H Q ⟨c.store, c.frame, L⟩) :
    Must H Q c := by
  have hs : ∃ c', Step H c c' := by
    rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, -⟩ | ⟨s', f', es', hh⟩
    · cases ha
    · exact ⟨⟨s', f', es'⟩, by simpa using seq_step (H := H) hh⟩
  refine Must.next hs ?_
  intro c' hstep
  obtain ⟨hstore, hframe, hsize, hh⟩ := step_throw hstep [] [] _ (by simpa using ht)
  rcases hh with hh | ⟨L', hL', hl⟩
  · exact must_throwHandler (by simpa using hh) (by simpa only [hstore, hframe] using hL)
  · cases hL'
    simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl
    obtain ⟨s', f', es'⟩ := c'
    dsimp only at hstore hframe hl
    subst hstore hframe hl
    exact hL
termination_by seqSize c.instrs

/-- A pending trap's administrative steps reach `[trap]`, store and frame kept. -/
theorem steps_trap {H : HostSem} {c : Config} (ht : seqTraps c.instrs = true) :
    Steps H c ⟨c.store, c.frame, [.trap]⟩ := by
  by_cases hf : c.instrs = [.trap]
  · obtain ⟨s, f, es⟩ := c
    dsimp only at hf ⊢
    subst hf
    exact .refl
  · rcases seqTraps_runs c.store c.frame [] c.instrs ht with hh | ⟨s', f', es', hh⟩
    · exact False.elim (hf (seqTraps_final ht hh).2)
    · have hstep : Step H c ⟨s', f', es'⟩ := by simpa using seq_step (H := H) hh
      obtain ⟨hstore, hframe, htrap, -⟩ := step_traps hstep [] (by simpa using ht)
      have hr := steps_trap (H := H) (c := ⟨s', f', es'⟩) (by simpa using htrap)
      dsimp only at hstore hframe hr
      rw [← hstore, ← hframe]
      exact .head hstep hr
termination_by seqSize c.instrs
decreasing_by
  obtain ⟨-, -, -, hsize⟩ := step_traps hstep [] (by simpa using ht)
  simpa using hsize

/-- A pending throw no handler encloses reaches `throwing a`, store and frame kept. -/
theorem steps_throw {H : HostSem} {c : Config} {a : Nat}
    (ht : seqThrow [] c.instrs = some (.inl a)) : Steps H c ⟨c.store, c.frame, throwing a⟩ := by
  by_cases hf : c.instrs = throwing a
  · obtain ⟨s, f, es⟩ := c
    dsimp only at hf ⊢
    subst hf
    exact .refl
  · rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, hh⟩ | ⟨s', f', es', hh⟩
    · cases ha
      exact False.elim (hf (by simpa using seq_thrown hh))
    · have hstep : Step H c ⟨s', f', es'⟩ := by simpa using seq_step (H := H) hh
      obtain ⟨hstore, hframe, -, hh'⟩ := step_throw hstep [] [] _ (by simpa using ht)
      rcases hh' with hh' | ⟨L, hL, -⟩
      · have hr := steps_throw (H := H) (c := ⟨s', f', es'⟩) (by simpa using hh')
        dsimp only at hstore hframe hr
        rw [← hstore, ← hframe]
        exact .head hstep hr
      · cases hL
termination_by seqSize c.instrs
decreasing_by
  obtain ⟨-, -, hsize, -⟩ := step_throw hstep [] [] _ (by simpa using ht)
  simpa using hsize

/-- A pending throw inside a handler reaches that handler (`L`), store and frame kept. -/
theorem steps_throwHandler {H : HostSem} {c : Config} {L : List AInstr}
    (ht : seqThrow [] c.instrs = some (.inr L)) : Steps H c ⟨c.store, c.frame, L⟩ := by
  rcases seqThrow_runs c.store c.frame [] c.instrs _ ht with ⟨a', ha, -⟩ | ⟨s', f', es', hh⟩
  · cases ha
  · have hstep : Step H c ⟨s', f', es'⟩ := by simpa using seq_step (H := H) hh
    obtain ⟨hstore, hframe, -, hh'⟩ := step_throw hstep [] [] _ (by simpa using ht)
    dsimp only at hstore hframe
    rcases hh' with hh' | ⟨L', hL', hl⟩
    · have hr := steps_throwHandler (H := H) (c := ⟨s', f', es'⟩) (by simpa using hh')
      dsimp only at hr
      rw [← hstore, ← hframe]
      exact .head hstep hr
    · cases hL'
      simp only [List.reverse_nil, List.map_nil, List.nil_append, List.append_nil] at hl
      subst hstore hframe hl
      exact .single hstep
termination_by seqSize c.instrs
decreasing_by
  obtain ⟨-, -, hsize, -⟩ := step_throw hstep [] [] _ (by simpa using ht)
  simpa using hsize

/-- `runDet`'s result is reached by an execution: its unique steps, trap propagation and throw
normalization are steps of the spec. -/
theorem runDet_steps {H : HostSem} {n : Nat} {c c' : Config} (h : runDet n c = some c') :
    Steps H c c' := by
  induction n generalizing c with
  | zero => simp only [runDet, reduceCtorEq] at h
  | succ n ih =>
    cases ht : seqTraps c.instrs with
    | true =>
      simp only [runDet, ht, Bool.cond_true] at h
      cases Option.some.inj h
      exact steps_trap ht
    | false =>
      simp only [runDet, ht, Bool.cond_false] at h
      cases hth : seqThrow [] c.instrs with
      | some r =>
        cases r with
        | inl a =>
          simp only [hth] at h
          cases Option.some.inj h
          exact steps_throw hth
        | inr L =>
          simp only [hth] at h
          exact (steps_throwHandler hth).trans (ih h)
      | none =>
        simp only [hth] at h
        cases hu : uniqueStep false c with
        | false => simp only [hu, Bool.cond_false, reduceCtorEq] at h
        | true =>
          simp only [hu, Bool.cond_true] at h
          cases hs : seq c.store c.frame [] c.instrs with
          | step s f es =>
            simp only [hs] at h
            exact .head (step_sound (by simp only [step, hs])) (ih h)
          | final =>
            simp only [hs] at h
            cases Option.some.inj h
            exact .refl
          | _ => simp only [hs, reduceCtorEq] at h

theorem instrUnique_le (fits : Bool) (i : Instr) (vs : List Val)
    (h : instrUnique false i vs = true) : instrUnique fits i vs = true := by
  unfold instrUnique at h ⊢
  split <;> simp_all

/-- A step unique under the strict growth policy (growth may always fail) is unique under every
policy: the policies differ in growth alone. -/
theorem seqUnique_le (fits : Bool) (s : Store) (f : Frame) (vs : List Val) (es : List AInstr)
    (h : seqUnique false s f vs es = true) : seqUnique fits s f vs es = true := by
  refine seqUnique.induct s
    (fun f vs es => seqUnique false s f vs es = true → seqUnique fits s f vs es = true)
    (fun f vs e rest => atUnique false s f vs e rest = true → atUnique fits s f vs e rest = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ f vs es h
  · intro f vs rest n cont body ih h; unfold atUnique at h ⊢; exact ih h
  · intro f vs rest n fi body ih h; unfold atUnique at h ⊢; exact ih h
  · intro f vs rest n cs body ih h; unfold atUnique at h ⊢; exact ih h
  · intro f vs rest a dt id hf h; unfold atUnique at h ⊢; simp [hf] at h
  · intro f vs rest a hf h; unfold atUnique at h ⊢; exact h
  · intro f rest a vs' h; unfold atUnique at h ⊢; exact h
  · intro f vs rest hv h; unfold atUnique at h ⊢; exact h
  · intro f vs rest i hi h
    rw [atUnique_plain hi] at h ⊢
    exact instrUnique_le fits i vs h
  · intro f vs rest h; unfold atUnique at h; simp at h
  · intro t f vs rest h1 h2 h3 h4 h5 h6 h7 h; unfold atUnique at h ⊢; split <;> simp_all
  · intro f vs _; rfl
  · intro f vs e rest v hv ih h; unfold seqUnique at h ⊢; simp only [hv] at h ⊢; exact ih h
  · intro f vs e rest hv ih h; unfold seqUnique at h ⊢; simp only [hv] at h ⊢; exact ih h

theorem uniqueStep_le (fits : Bool) {c : Config} (h : uniqueStep false c = true) :
    uniqueStep fits c = true :=
  seqUnique_le fits c.store c.frame [] c.instrs h

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
      cases hth : seqThrow [] c.instrs with
      | some r =>
        cases r with
        | inl a =>
          simp only [hth] at h
          have he := Option.some.inj h
          subst c'
          exact must_throw hth (hQ (.thrown c.store a) ⟨rfl, rfl⟩)
        | inr L =>
          simp only [hth] at h
          exact must_throwHandler hth (ih h)
      | none =>
        simp only [hth] at h
        cases hu : uniqueStep false c with
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

theorem _root_.FVA.Wasm.Exec.Val.instr_inj {v w : Val} : v.instr = w.instr ↔ v = w := by
  constructor
  · intro h
    have := congrArg toVal h
    rwa [toVal_instr, toVal_instr, Option.some.injEq] at this
  · rintro rfl; rfl

theorem _root_.FVA.Wasm.Exec.vals_inj {vs ws : List Val} : vals vs = vals ws ↔ vs = ws := by
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun _ _ h => Val.instr_inj.mp h) h
  · rintro rfl; rfl

theorem _root_.FVA.Wasm.Exec.vals_ne_trap (vs : List Val) : vals vs ≠ [.trap] := by
  rcases vs with _ | ⟨v, vs⟩
  · simp [vals]
  · intro h
    have := congrArg List.head? h
    simp only [vals, List.map_cons, List.head?_cons, Option.some.injEq] at this
    have hv := congrArg toVal this
    have ht : toVal AInstr.trap = none := rfl
    rw [toVal_instr, ht] at hv
    cases hv

theorem no_step_values {H : HostSem} {s : Store} {f : Frame} {vs : List Val} {c : Config} :
    ¬Step H ⟨s, f, vals vs⟩ c := by
  intro hs
  have hu : seqUnique false s f [] (vals vs ++ []) = true := by
    rw [seqUnique_vals]
    rfl
  have hc := seq_complete hs [] [] hu
  simp [seq_values] at hc

theorem steps_values {H : HostSem} {s : Store} {f : Frame} {vs : List Val} {c : Config}
    (h : Steps H ⟨s, f, vals vs⟩ c) : c = ⟨s, f, vals vs⟩ := by
  induction h with
  | refl => rfl
  | tail h hs ih =>
    subst_vars
    exact False.elim (no_step_values hs)

theorem no_step_trap {H : HostSem} {s : Store} {f : Frame} {c : Config} :
    ¬Step H ⟨s, f, [.trap]⟩ c := by
  intro hs
  obtain ⟨-, -, ht, hsize⟩ := step_traps hs [] rfl
  rw [List.append_nil] at ht
  have h0 : seqSize c.instrs = 0 := by simp only [seqSize, adminSize] at hsize; omega
  rw [(seqSize_zero _).mp h0] at ht
  exact absurd ht (by decide)

theorem no_step_throwing {H : HostSem} {s : Store} {f : Frame} {a : Nat} {c : Config} :
    ¬Step H ⟨s, f, throwing a⟩ c := by
  intro hs
  have hc := seq_complete hs [] [] rfl
  simp [throwing] at hc

theorem _root_.FVA.Wasm.Exec.vals_ne_throwing (vs : List Val) (a : Nat) :
    vals vs ≠ throwing a := by
  intro h
  rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
  · simp [vals, throwing] at h
  · simp [vals, throwing] at h
  · simp only [vals, List.map_cons, throwing, List.cons.injEq] at h
    have hw := congrArg toVal h.2.1
    rw [toVal_instr] at hw
    simp [toVal] at hw

/-- A finished configuration has no successor. -/
theorem no_step_final {H : HostSem} {c c' : Config} {o : Outcome} (hf : Final c o) :
    ¬Step H c c' := by
  obtain ⟨s, f, es⟩ := c
  cases o with
  | returned s' vs => obtain ⟨-, rfl⟩ := hf; exact no_step_values
  | trapped s' => obtain ⟨-, rfl⟩ := hf; exact no_step_trap
  | thrown s' a => obtain ⟨-, rfl⟩ := hf; exact no_step_throwing

theorem final_unique {c : Config} {o o' : Outcome} (h : Final c o) (h' : Final c o') : o = o' := by
  cases o <;> cases o' <;> obtain ⟨hs, hi⟩ := h <;> obtain ⟨hs', hi'⟩ := h'
  · rw [← hs, ← hs', vals_inj.mp (hi.symm.trans hi')]
  · exact absurd (hi.symm.trans hi') (vals_ne_trap _)
  · exact absurd (hi.symm.trans hi') (vals_ne_throwing _ _)
  · exact absurd (hi'.symm.trans hi) (vals_ne_trap _)
  · rw [← hs, ← hs']
  · exact absurd (hi.symm.trans hi') (by simp [throwing])
  · exact absurd (hi'.symm.trans hi) (vals_ne_throwing _ _)
  · exact absurd (hi'.symm.trans hi) (by simp [throwing])
  · have he := hi.symm.trans hi'
    simp only [throwing, List.cons.injEq, AInstr.refExnAddr.injEq, and_true] at he
    rw [← hs, ← hs', he]

/-- Every finished execution from a `Must` start has an outcome satisfying its postcondition:
`Must` fixes the outcome of every run, so a run that `Steps` names ends in one of them. -/
theorem _root_.FVA.Wasm.Exec.Must.outcome {H : HostSem} {Q : Outcome → Prop} {c d : Config}
    {o : Outcome} (hm : Must H Q c) (hs : Steps H c d) (hf : Final d o) : Q o := by
  induction hm with
  | done hc hq =>
    rcases hs.cases_head with rfl | ⟨_, h, _⟩
    · exact final_unique hc hf ▸ hq
    · exact absurd h (no_step_final hc)
  | @next c₀ hex hnext ih =>
    rcases hs.cases_head with rfl | ⟨c₁, h, hrest⟩
    · obtain ⟨_, h⟩ := hex; exact absurd h (no_step_final hf)
    · exact ih c₁ h hrest

end FVA.Wasm.Exec.Ref
