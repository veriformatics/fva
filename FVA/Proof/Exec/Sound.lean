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

theorem prependInner_fill {k : Nat} (L : BlockCtx k) (extra : List Val) (es : List AInstr) :
    (prependInner L extra).fill es = L.fill (vals extra ++ es) := by
  induction L with
  | base vs rest => simp [prependInner, BlockCtx.fill, List.map_append, List.append_assoc]
  | label vs n cont inner rest ih => simp [prependInner, BlockCtx.fill, ih]

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
  | .final => es = [.trap] ∨ ∃ ws, es = vals ws
  | .stuck => True

theorem vals_reverse_split (vs : List Val) (n : Nat) :
    vals vs.reverse = vals (vs.drop n).reverse ++ vals (vs.take n).reverse := by
  rw [← List.map_append, ← List.reverse_append, List.take_append_drop]

theorem atInstr_plain {s : Store} {f : Frame} {vs : List Val} {i : Instr}
    {rest : List AInstr} (hb : ∀ k, i ≠ .br k) (hr : i ≠ .return_) :
    atInstr s f vs (.plain i) rest =
      match instrStep s f i vs with
      | some (s', f', stk, out) => .step s' f' (vals stk.reverse ++ out ++ rest)
      | none => .stuck := by
  cases i <;> first | rfl | simp_all

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
      (Step.trap (H := H) (s := s) (f := f) (.seq vs.reverse .hole rest) hctx)
  case case3 =>
    intro f vs rest n cont body he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    rcases ih with rfl | ⟨ws, rfl⟩
    · simpa only [isTrapOnly, Bool.cond_true, EvalCtx.fill, List.append_assoc,
        List.singleton_append] using
        (Step.seq (vs := vs.reverse) (rest := rest)
          (Step.trap (H := H) (s := s) (f := f) (.label n cont .hole)
            (by simp [EvalCtx.fill])))
    · simp only [isTrapOnly_vals, Bool.cond_false]
      simpa only [List.append_assoc, List.singleton_append] using
        (Step.seq (vs := vs.reverse) (rest := rest)
          (Step.labelExit (H := H) (s := s) (f := f) (n := n) (cont := cont) (vs := ws)))
  case case4 =>
    intro f vs rest n cont body s' f' body' he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := vs.reverse) (rest := rest) (Step.label (n := n) (cont := cont) ih))
  case case5 =>
    intro f vs rest n cont body bvs he hb _
    simp only [atInstr, he, hb, Bool.cond_true, Explains]
  case case6 =>
    intro f vs rest n cont body bvs he hb ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append, Nat.add_zero] at ih
    simp only [atInstr, he, hb, Bool.cond_false, Explains]
    rcases ih with ⟨j, L, hbody⟩
    have hs := Step.br (H := H) (s := s) (f := f) (n := n) (cont := cont)
      (vs := (bvs.take n).reverse) (prependInner L (bvs.drop n).reverse)
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [prependInner_take, ← hbody] at hs
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := vs.reverse) (rest := rest) hs)
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
    intro f vs rest n cont body he _
    simp only [atInstr, he, Explains]
  case case10 =>
    intro f vs rest n fi body he ht _
    simp only [atInstr, he, ht, Bool.cond_true, Explains]
    have hbody := isTrapOnly_eq_true.mp ht
    subst body
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := vs.reverse) (rest := rest)
        (Step.trapFrame (H := H) (s := s) (f := f) (n := n) (fi := fi)))
  case case11 =>
    intro f vs rest n fi body he ht hn ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, ht, hn, Bool.cond_false, Bool.cond_true, Explains]
    rcases ih with hbody | ⟨ws, rfl⟩
    · simp only [hbody, isTrapOnly] at ht
      contradiction
    · have hlen : ws.length = n := by simpa using Nat.beq_eq.mp hn
      simpa only [List.append_assoc, List.singleton_append] using
        (Step.seq (vs := vs.reverse) (rest := rest)
          (Step.frameExit (H := H) (s := s) (f := f) (f' := fi) hlen))
  case case12 =>
    intro f vs rest n fi body he ht hn _
    simp only [atInstr, he, ht, hn, Bool.cond_false, Explains]
  case case13 =>
    intro f vs rest n fi body s' fi' body' he ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, Explains]
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := vs.reverse) (rest := rest) (Step.frame (f := f) (n := n) ih))
  case case14 =>
    intro f vs rest n fi body bvs he hb _
    simp only [atInstr, he, hb, Bool.cond_true, Explains]
  case case15 =>
    intro f vs rest n fi body bvs he hb ih
    simp only [he, Explains, List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [atInstr, he, hb, Bool.cond_false, Explains]
    rcases ih with ⟨j, L, hbody⟩
    have hs := Step.return_ (H := H) (s := s) (f := f) (n := n) (f' := fi)
      (vs := (bvs.take n).reverse) (prependInner L (bvs.drop n).reverse)
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [prependInner_take, ← hbody] at hs
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := vs.reverse) (rest := rest) hs)
  case case16 =>
    intro f vs rest n fi body k bvs he _
    simp only [atInstr, he, Explains]
  case case17 =>
    intro f vs rest n fi body he _
    simp only [atInstr, he, Explains]
  case case18 =>
    intro f vs rest a ft inst code hf m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hb, Bool.cond_true, Explains]
  case case19 =>
    intro f vs rest a ft inst code hf m hb
    dsimp only [m] at hb
    simp only [atInstr, hf, hb, Bool.cond_false, Explains]
    have hs := Step.invoke (H := H) (f := f) (vs := (vs.take ft.params.length).reverse) hf
      (by simp [Nat.min_eq_left (nblt_false.mp hb)])
    rw [vals_reverse_split vs ft.params.length]
    simpa only [List.append_assoc, List.singleton_append] using
      (Step.seq (vs := (vs.drop ft.params.length).reverse) (rest := rest) hs)
  case case20 =>
    intro f vs rest a hf
    simp_all only [atInstr, Explains]
  case case21 =>
    intro f vs rest k
    refine ⟨0, .base [] rest, ?_⟩
    simp only [BlockCtx.fill, List.map_nil, List.nil_append, Nat.zero_add,
      List.append_assoc, List.singleton_append]
  case case22 =>
    intro f vs rest
    refine ⟨0, .base [] rest, ?_⟩
    simp only [BlockCtx.fill, List.map_nil, List.nil_append,
      List.append_assoc, List.singleton_append]
  case case23 =>
    intro f vs rest i hb hr s' f' stk out hi
    rw [atInstr_plain hb hr, hi]
    simp only [Explains]
    rcases instrStep_sound (H := H) hi with ⟨args, hvs, hs⟩
    rw [hvs]
    simpa only [List.reverse_append, List.reverse_reverse, List.map_append,
      List.append_assoc, List.singleton_append] using
      (Step.seq (vs := stk.reverse) (rest := rest) hs)
  case case24 =>
    intro f vs rest i hb hr hi
    rw [atInstr_plain hb hr, hi]
    trivial
  case case25 =>
    intro t f vs rest ht hl hf hi hb hr hp
    cases t <;> simp_all [atInstr, Explains]
  case case26 =>
    intro f vs
    exact Or.inr ⟨vs.reverse, List.append_nil _⟩
  case case27 =>
    intro f vs e rest v hv ih
    simp only [seq, hv]
    have he := eq_instr_of_toVal hv
    subst e
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] using ih
  case case28 =>
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
    · contradiction

end FVA.Wasm.Exec.Ref
