import FVA.Proof.Exec.SoundLemmas
import FVA.Spec.Claims

/-!
# The reference stepper is sound

Every step `Ref.seq` returns is a `Step` of the spec (for every host relation: the stepper never
calls a host); its `br`/`ret` signals stand for a block context around the branch; a run that
reaches a final configuration is a `Steps` reduction to it.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Num

/-- Add values at the innermost hole of a block context. -/
def prependInner : {k : Nat} → BlockCtx k → List Val → BlockCtx k
  | _, .base vs rest, extra => .base (vs ++ extra) rest
  | _, .label vs n cont inner rest, extra =>
    .label vs n cont (prependInner inner extra) rest
  | _, .handler vs n cs inner rest, extra =>
    .handler vs n cs (prependInner inner extra) rest

theorem prependInner_fill {k : Nat} (L : BlockCtx k) (extra : List Val) (es : List AInstr) :
    (prependInner L extra).fill es = L.fill (vals extra ++ es) := by
  induction L with
  | base vs rest => simp [prependInner, BlockCtx.fill, List.map_append, List.append_assoc]
  | label vs n cont inner rest ih => simp [prependInner, BlockCtx.fill, ih]
  | handler vs n cs inner rest ih => simp [prependInner, BlockCtx.fill, ih]

theorem prependInner_take {k : Nat} (L : BlockCtx k) (vs : List Val) (n : Nat)
    (es : List AInstr) :
    (prependInner L (vs.drop n).reverse).fill (vals (vs.take n).reverse ++ es) =
      L.fill (vals vs.reverse ++ es) := by
  rw [prependInner_fill, ← List.append_assoc, ← List.map_append,
    ← List.reverse_append, List.take_append_drop]

theorem vals_append_eq_trap {vs : List Val} {es : List AInstr}
    (h : vals vs ++ es = [.trap]) : vs = [] ∧ es = [.trap] := by
  cases vs with
  | nil => exact ⟨rfl, h⟩
  | cons v vs =>
    have hv : v.instr = .trap := (List.cons.inj h).1
    have := congrArg toVal hv
    rw [toVal_instr] at this
    contradiction

theorem isTrapOnly_eq_true {es : List AInstr} : isTrapOnly es = true ↔ es = [.trap] := by
  fun_cases isTrapOnly es <;> simp_all

theorem isTrapOnly_vals (vs : List Val) : isTrapOnly (vals vs) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := isTrapOnly_eq_true.mp h
  have hs := vals_append_eq_trap (es := []) (by simpa using he)
  cases hs.2

/-- A reference result denotes one reduction, a pending control transfer, or a final form. -/
def Explains (H : HostSem) (s : Store) (f : Frame) (es : List AInstr) : Out → Prop
  | .step s' f' es' => Step H ⟨s, f, es⟩ ⟨s', f', es'⟩
  | .br k bvs => ∃ j, ∃ L : BlockCtx j,
    es = L.fill (vals bvs.reverse ++ [.plain (.br (j + k))])
  | .ret bvs => ∃ j, ∃ L : BlockCtx j,
    es = L.fill (vals bvs.reverse ++ [.plain .return_])
  | .retInvoke a args => ∃ fn ft, s.funcs[a]? = some fn ∧ fn.type.expand = some ft ∧
    args.length = ft.params.length ∧ ∃ j, ∃ L : BlockCtx j,
    es = L.fill (vals args ++ [.returnInvoke a])
  | .thrown a => es = throwing a
  | .final => es = [.trap] ∨ ∃ ws, es = vals ws
  | .host a args k => ∃ dt ft id, s.funcs[a]? = some (.host dt id) ∧ dt.expand = some ft ∧
    args.length = ft.params.length ∧ es = k.fill (vals args ++ [.invoke a])
  | .stuck => True

theorem vals_reverse_split (vs : List Val) (n : Nat) :
    vals vs.reverse = vals (vs.drop n).reverse ++ vals (vs.take n).reverse := by
  rw [← List.map_append, ← List.reverse_append, List.take_append_drop]

theorem atInstr_plain {s : Store} {f : Frame} {vs : List Val} {i : Instr}
    {rest : List AInstr} (hb : ∀ k, i ≠ .br k) (hr : i ≠ .return_) (ht : i ≠ .throwRef) :
    atInstr s f vs (.plain i) rest =
      match instrStep s f i vs with
      | some (s', f', stk, out) => .step s' f' (vals stk.reverse ++ out ++ rest)
      | none => .stuck := by
  cases i <;> first | rfl | simp_all

/-- A handler clause the stepper takes is a spec step of the handler around the throw. -/
theorem catchStep_sound {H : HostSem} {s : Store} {f : Frame} {a n : Nat} {c : Catch}
    {cs : List Catch} {out : List AInstr} (h : catchStep s f a c = some out) :
    Step H ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ ⟨s, f, out⟩ := by
  cases c with
  | tag x l =>
    simp only [catchStep] at h
    split at h <;> try contradiction
    rename_i e ta he hta
    cases hb : (ta == e.tag) <;> simp only [hb, Bool.cond_false, Bool.cond_true, reduceCtorEq,
      Option.some.injEq] at h
    subst out
    exact StepP.throwRefCatch he (by rw [hta, beq_iff_eq.mp hb])
  | tagRef x l =>
    simp only [catchStep] at h
    split at h <;> try contradiction
    rename_i e ta he hta
    cases hb : (ta == e.tag) <;> simp only [hb, Bool.cond_false, Bool.cond_true, reduceCtorEq,
      Option.some.injEq] at h
    subst out
    exact StepP.throwRefCatchRef he (by rw [hta, beq_iff_eq.mp hb])
  | all l =>
    cases h
    exact StepP.throwRefCatchAll
  | allRef l =>
    cases h
    exact StepP.throwRefCatchAllRef

/-- A clause the stepper skips does not take the exception. -/
theorem catchStep_none {s : Store} {f : Frame} {a : Nat} {c : Catch}
    (h : catchStep s f a c = none) : ¬ c.Catches s f a := by
  cases c with
  | tag x l | tagRef x l =>
    rintro ⟨e, he, hta⟩
    simp [catchStep, he, hta] at h
  | all l | allRef l => cases h

set_option maxHeartbeats 2000000 in
theorem seq_explains (H : HostSem) (s : Store) (f : Frame) (vs : List Val)
    (es : List AInstr) : Explains H s f (vals vs.reverse ++ es) (seq s f vs es) := by
  apply seq.induct s
    (motive_1 := fun f vs es => Explains H s f (vals vs.reverse ++ es) (seq s f vs es))
    (motive_2 := fun f vs e rest =>
      Explains H s f (vals vs.reverse ++ e :: rest) (atInstr s f vs e rest))
  case case1 =>
    intro f vs rest ht
    simp only [Bool.and_eq_true, List.isEmpty_iff] at ht
    rcases ht with ⟨rfl, rfl⟩
    exact Or.inl rfl
  case case2 =>
    intro f vs rest ht
    simp only [atInstr, ht, Bool.cond_false, Explains]
    have hne : vs.reverse ≠ [] ∨ rest ≠ [] := by
      by_cases hv : vs = [] <;> simp_all
    have hctx : (EvalCtx.seq vs.reverse .hole rest).fill [.trap] ≠ [.trap] := by
      intro he
      rcases vals_append_eq_trap (by
        simpa only [EvalCtx.fill, List.append_assoc, List.singleton_append] using he) with
        ⟨hv, hr⟩
      exact hne.elim (fun h => h hv) (fun h => h (List.cons.inj hr).2)
    simpa only [EvalCtx.fill, List.append_assoc, List.singleton_append] using
      (StepP.trap (H := H) (fits := false) (s := s) (f := f) (.seq vs.reverse .hole rest) hctx)
  case case3 =>
    intro f vs rest n cont body he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with rfl | ⟨ws, rfl⟩
    · simpa only [isTrapOnly, Bool.cond_true, EvalCtx.fill, List.append_assoc,
        List.singleton_append] using
        (StepP.seq (vs := vs.reverse) (rest := rest)
          (StepP.trap (H := H) (fits := false) (s := s) (f := f) (.label n cont .hole)
            (by simp [EvalCtx.fill])))
    · simp only [isTrapOnly_vals, Bool.cond_false]
      simpa only [List.append_assoc, List.singleton_append] using
        (StepP.seq (vs := vs.reverse) (rest := rest)
          (StepP.labelExit (H := H) (fits := false) (s := s) (f := f) (n := n) (cont := cont)
            (vs := ws)))
  case case4 =>
    intro f vs rest n cont body s' f' body' he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest) (StepP.label (n := n) (cont := cont) ih))
  case case5 =>
    intro f vs rest n cont body bvs he hb _
    simp only [atInstr, he, hb, Bool.cond_true, Explains]
  case case6 =>
    intro f vs rest n cont body bvs he hb ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append, Nat.add_zero] at ih
    simp only [atInstr, he, hb, Bool.cond_false, Explains]
    rcases ih with ⟨j, L, hbody⟩
    have hs := StepP.br (H := H) (fits := false) (s := s) (f := f) (n := n) (cont := cont)
      (vs := (bvs.take n).reverse) (prependInner L (bvs.drop n).reverse)
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [prependInner_take, ← hbody] at hs
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest) hs)
  case case7 =>
    intro f vs rest n cont body k bvs he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨j, L, hbody⟩
    refine ⟨j + 1, .label vs.reverse n cont L rest, ?_⟩
    have hi : j + k.succ = (j + 1) + k := by omega
    simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody, hi]
  case case8 =>
    intro f vs rest n cont body bvs he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨j, L, hbody⟩
    refine ⟨j + 1, .label vs.reverse n cont L rest, ?_⟩
    simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody]
  case case9 =>
    intro f vs rest n cont body a args he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨fn, ft, hfn, hft, hlen, j, L, hbody⟩
    exact ⟨fn, ft, hfn, hft, hlen, j + 1, .label vs.reverse n cont L rest,
      by simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody]⟩
  case case10 =>
    intro f vs rest n cont body a he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.throwRefLabel (H := H) (fits := false) (s := s) (f := f) (a := a) (n := n)
          (cont := cont)))
  case case11 =>
    intro f vs rest n cont body a args k he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨dt, ft, id, hf, hft, hlen, hbody⟩
    exact ⟨dt, ft, id, hf, hft, hlen, by simp [HCtx.fill, hbody]⟩
  case case12 =>
    intro f vs rest n cont body he _
    simp only [atInstr, he, Explains]
  case case13 =>
    intro f vs rest n fi body he ht _
    simp only [atInstr, he, ht, Bool.cond_true, Explains]
    have hbody := isTrapOnly_eq_true.mp ht
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.trapFrame (H := H) (fits := false) (s := s) (f := f) (n := n) (fi := fi)))
  case case14 =>
    intro f vs rest n fi body he ht hn ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, ht, hn, Bool.cond_false, Bool.cond_true, Explains]
    rcases ih with hbody | ⟨ws, rfl⟩
    · simp only [hbody, isTrapOnly] at ht
      contradiction
    · have hlen : ws.length = n := by simpa using Nat.beq_eq.mp hn
      simpa only [List.append_assoc, List.singleton_append] using
        (StepP.seq (vs := vs.reverse) (rest := rest)
          (StepP.frameExit (H := H) (fits := false) (s := s) (f := f) (f' := fi) hlen))
  case case15 =>
    intro f vs rest n fi body he ht hn _
    simp only [atInstr, he, ht, hn, Bool.cond_false, Explains]
  case case16 =>
    intro f vs rest n fi body s' fi' body' he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest) (StepP.frame (f := f) (n := n) ih))
  case case17 =>
    intro f vs rest n fi body bvs he hb _
    simp only [atInstr, he, hb, Bool.cond_true, Explains]
  case case18 =>
    intro f vs rest n fi body bvs he hb ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, hb, Bool.cond_false, Explains]
    rcases ih with ⟨j, L, hbody⟩
    have hs := StepP.return_ (H := H) (fits := false) (s := s) (f := f) (n := n) (f' := fi)
      (vs := (bvs.take n).reverse) (prependInner L (bvs.drop n).reverse)
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [prependInner_take, ← hbody] at hs
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest) hs)
  case case19 =>
    intro f vs rest n fi body a args he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨fn, ft, hfn, hft, hlen, j, L, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.returnInvoke (H := H) (fits := false) (s := s) (f := f) (n := n) (fi := fi) L hfn
          hft hlen))
  case case20 =>
    intro f vs rest n fi body a he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.throwRefFrame (H := H) (fits := false) (s := s) (f := f) (a := a) (n := n)
          (fi := fi)))
  case case21 =>
    intro f vs rest n fi body k bvs he _
    simp only [atInstr, he, Explains]
  case case22 =>
    intro f vs rest n fi body a args k he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨dt, ft, id, hf, hft, hlen, hbody⟩
    exact ⟨dt, ft, id, hf, hft, hlen, by simp [HCtx.fill, hbody]⟩
  case case23 =>
    intro f vs rest n fi body he _
    simp only [atInstr, he, Explains]
  case case24 =>
    intro f vs rest n cs body he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with rfl | ⟨ws, rfl⟩
    · simpa only [isTrapOnly, Bool.cond_true, EvalCtx.fill, List.append_assoc,
        List.singleton_append] using
        (StepP.seq (vs := vs.reverse) (rest := rest)
          (StepP.trap (H := H) (fits := false) (s := s) (f := f) (.handler n cs .hole)
            (by simp [EvalCtx.fill])))
    · simp only [isTrapOnly_vals, Bool.cond_false]
      simpa only [List.append_assoc, List.singleton_append] using
        (StepP.seq (vs := vs.reverse) (rest := rest)
          (StepP.handlerExit (H := H) (fits := false) (s := s) (f := f) (n := n) (cs := cs)
            (vs := ws)))
  case case25 =>
    intro f vs rest n cs body s' f' body' he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest) (StepP.handler (n := n) (cs := cs) ih))
  case case26 =>
    intro f vs rest n cs body k bvs he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨j, L, hbody⟩
    exact ⟨j, .handler vs.reverse n cs L rest,
      by simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody]⟩
  case case27 =>
    intro f vs rest n cs body bvs he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨j, L, hbody⟩
    exact ⟨j, .handler vs.reverse n cs L rest,
      by simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody]⟩
  case case28 =>
    intro f vs rest n cs body a args he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨fn, ft, hfn, hft, hlen, j, L, hbody⟩
    exact ⟨fn, ft, hfn, hft, hlen, j, .handler vs.reverse n cs L rest,
      by simp only [BlockCtx.fill, List.append_assoc, List.singleton_append, hbody]⟩
  case case29 =>
    intro f vs rest n body a he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.throwRefHandlerEmpty (H := H) (fits := false) (s := s) (f := f) (a := a)
          (n := n)))
  case case30 =>
    intro f vs rest n body a he c cs' out hc ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, hc, Explains]
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (catchStep_sound (H := H) (n := n) (cs := cs') hc))
  case case31 =>
    intro f vs rest n body a he c cs' hc ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, hc, Explains]
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := vs.reverse) (rest := rest)
        (StepP.throwRefHandlerNext (H := H) (fits := false) (n := n) (cs := cs')
          (catchStep_none hc)))
  case case32 =>
    intro f vs rest n cs body a args k he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with ⟨dt, ft, id, hf, hft, hlen, hbody⟩
    exact ⟨dt, ft, id, hf, hft, hlen, by simp [HCtx.fill, hbody]⟩
  case case33 =>
    intro f vs rest n cs body he _
    simp only [atInstr, he, Explains]
  case case34 =>
    intro f vs rest a fn hfn ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hfn, hft, hb, Bool.cond_true, Explains]
  case case35 =>
    intro f vs rest a fn hfn ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hfn, hft, hb, Bool.cond_false, Explains]
    refine ⟨fn, ft, rfl, hft, by simp [Nat.min_eq_left (nblt_false.mp hb)], 0,
      .base (vs.drop ft.params.length).reverse rest, ?_⟩
    rw [vals_reverse_split vs ft.params.length]
    simp [BlockCtx.fill, List.append_assoc]
  case case36 =>
    intro f vs rest a fn hfn hft
    simp only [atInstr, hfn, hft, Explains]
  case case37 =>
    intro f vs rest a hfn
    simp only [atInstr, hfn, Explains]
  case case38 =>
    intro f vs rest a dt inst code hf ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hft, hb, Bool.cond_true, Explains]
  case case39 =>
    intro f vs rest a dt inst code hf ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hft, hb, Bool.cond_false, Explains]
    have hs := StepP.invoke (H := H) (fits := false) (f := f)
      (vs := (vs.take ft.params.length).reverse) hf hft
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [vals_reverse_split vs ft.params.length]
    simpa only [List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := (vs.drop ft.params.length).reverse) (rest := rest) hs)
  case case40 =>
    intro f vs rest a dt inst code hf hft
    simp only [atInstr, hf, hft, Explains]
  case case41 =>
    intro f vs rest a dt id hf ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hft, hb, Bool.cond_true, Explains]
  case case42 =>
    intro f vs rest a dt id hf ft hft m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hft, hb, Bool.cond_false, Explains]
    refine ⟨dt, ft, id, rfl, hft, by simp [Nat.min_eq_left (nblt_false.mp hb)], ?_⟩
    rw [vals_reverse_split vs ft.params.length]
    simp [HCtx.fill, List.append_assoc]
  case case43 =>
    intro f vs rest a dt id hf hft
    simp only [atInstr, hf, hft, Explains]
  case case44 =>
    intro f vs rest a hf
    simp only [atInstr, hf, Explains]
  case case45 =>
    intro f vs rest k
    refine ⟨0, .base [] rest, ?_⟩
    simp only [BlockCtx.fill, List.map_nil, List.nil_append, Nat.zero_add,
      List.append_assoc, List.singleton_append]
  case case46 =>
    intro f vs rest
    refine ⟨0, .base [] rest, ?_⟩
    simp only [BlockCtx.fill, List.map_nil, List.nil_append,
      List.append_assoc, List.singleton_append]
  case case47 =>
    intro f rest a vs' he
    simp only [Bool.and_eq_true, List.isEmpty_iff] at he
    rcases he with ⟨rfl, rfl⟩
    simp only [atInstr, Explains, List.isEmpty_nil, Bool.and_self, Bool.cond_true]
    rfl
  case case48 =>
    intro f rest a vs' he
    simp only [atInstr, he, Bool.cond_false, Explains]
    have hne : vs'.reverse ≠ [] ∨ rest ≠ [] := by
      by_cases hv : vs' = [] <;> simp_all
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, Val.instr,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      (StepP.throwRefInstrs (H := H) (fits := false) (s := s) (f := f) (a := a) hne)
  case case49 =>
    intro f rest vs'
    simp only [atInstr, Explains]
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, Val.instr,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      (StepP.seq (vs := vs'.reverse) (rest := rest)
        (StepP.throwRefNull (H := H) (fits := false) (s := s) (f := f)))
  case case50 =>
    intro f vs rest h₁ h₂
    simp only [atInstr]
    trivial
  case case51 =>
    intro f vs rest i hb hr ht s' f' stk out hi
    rw [atInstr_plain hb hr ht, hi]
    simp only [Explains]
    rcases instrStep_sound (H := H) hi with ⟨args, hvs, hs⟩
    rw [hvs]
    simpa only [List.reverse_append, List.reverse_reverse, List.map_append,
      List.append_assoc, List.singleton_append] using
      (StepP.seq (vs := stk.reverse) (rest := rest) hs)
  case case52 =>
    intro f vs rest i hb hr ht hi
    rw [atInstr_plain hb hr ht, hi]
    trivial
  case case53 =>
    intro t f vs rest ht hl hf hh hr hi hb hret hthr hp
    cases t <;> simp_all [atInstr, Explains]
  case case54 =>
    intro f vs
    exact Or.inr ⟨vs.reverse, List.append_nil _⟩
  case case55 =>
    intro f vs e rest v hv ih
    simp only [seq, hv]
    have he := eq_instr_of_toVal hv
    subst e
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using ih
  case case56 =>
    intro f vs e rest hv ih
    simp only [seq, hv]
    exact ih

theorem seq_step {H : HostSem} {s s' : Store} {f f' : Frame} {vs : List Val}
    {es es' : List AInstr} (h : seq s f vs es = .step s' f' es') :
    Step H ⟨s, f, vals vs.reverse ++ es⟩ ⟨s', f', es'⟩ := by
  simpa only [h, Explains] using seq_explains H s f vs es

theorem seq_final {s : Store} {f : Frame} {vs : List Val} {es : List AInstr}
    (h : seq s f vs es = .final) :
    (vs = [] ∧ es = [.trap]) ∨ ∃ ws, vals vs.reverse ++ es = vals ws := by
  have hs := seq_explains (fun _ _ _ _ => False) s f vs es
  simp only [h, Explains] at hs
  rcases hs with ht | hw
  · rcases vals_append_eq_trap ht with ⟨hv, he⟩
    exact Or.inl ⟨by simpa using hv, he⟩
  · exact Or.inr hw

theorem seq_br {s : Store} {f : Frame} {vs bvs : List Val} {es : List AInstr} {k : Nat}
    (h : seq s f vs es = .br k bvs) :
    ∃ j, ∃ L : BlockCtx j,
      vals vs.reverse ++ es = L.fill (vals bvs.reverse ++ [.plain (.br (j + k))]) := by
  simpa only [h, Explains] using seq_explains (fun _ _ _ _ => False) s f vs es

theorem seq_thrown {s : Store} {f : Frame} {vs : List Val} {es : List AInstr} {a : Nat}
    (h : seq s f vs es = .thrown a) : vals vs.reverse ++ es = throwing a := by
  simpa only [h, Explains] using seq_explains (fun _ _ _ _ => False) s f vs es

theorem seq_ret {s : Store} {f : Frame} {vs bvs : List Val} {es : List AInstr}
    (h : seq s f vs es = .ret bvs) :
    ∃ j, ∃ L : BlockCtx j,
      vals vs.reverse ++ es = L.fill (vals bvs.reverse ++ [.plain .return_]) := by
  simpa only [h, Explains] using seq_explains (fun _ _ _ _ => False) s f vs es

theorem step_sound {H : HostSem} {c c' : Config} (h : step c = some c') : Step H c c' := by
  simp only [step] at h
  split at h
  · rename_i s f es hs
    cases h
    simpa only [List.reverse_nil, List.map_nil, List.nil_append] using seq_step (H := H) hs
  · contradiction

theorem run_sound {H : HostSem} {n : Nat} {c c' : Config} (h : run n c = some c') :
    Steps H c c' ∧ ∃ o, Final c' o := by
  induction n generalizing c with
  | zero => simp only [run, reduceCtorEq] at h
  | succ n ih =>
    simp only [run] at h
    split at h
    · rename_i s f es hs
      have hstep : Step H c ⟨s, f, es⟩ := by
        simpa only [List.reverse_nil, List.map_nil, List.nil_append] using seq_step (H := H) hs
      rcases ih h with ⟨hsteps, hfinal⟩
      exact ⟨Relation.ReflTransGen.head hstep hsteps, hfinal⟩
    · rename_i hs
      have hc := Option.some.inj h
      subst c'
      rcases seq_final hs with ⟨_, ht⟩ | ⟨ws, hv⟩
      · exact ⟨.refl, .trapped c.store, rfl, ht⟩
      · exact ⟨.refl, .returned c.store ws, rfl, by simpa using hv⟩
    · rename_i a hs
      have hc := Option.some.inj h
      subst c'
      exact ⟨.refl, .thrown c.store a, rfl, by simpa using seq_thrown hs⟩
    · contradiction

end FVA.Wasm.Exec.Ref
