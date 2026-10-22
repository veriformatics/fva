import FVA.Proof.Exec.Sound

/-!
# The executable instantiation is sound

`Ref.instantiate` with matching imports yields a store and instance the spec's `Instantiated`
relates to the module: its constant-expression evaluations are reductions that keep the store and
frame, the final allocation is `allocModule`'s, and the initialization code reduces to nothing.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- An administrative value or one of the constant-expression instructions. -/
def ConstInstr : AInstr → Prop
  | .plain i => isConstInstr i = true
  | .refFuncAddr _ | .refExternAddr _ => True
  | _ => False

theorem constInstr_val (v : Val) : ConstInstr v.instr := by
  cases v with
  | ref r => cases r <;> trivial
  | _ => rfl

theorem constInstr_vals (vs : List Val) : ∀ a ∈ vals vs, ConstInstr a := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨v, _, rfl⟩
  exact constInstr_val v

theorem atInstr_const {s s' : Store} {f f' : Frame} {vs : List Val} {i : Instr}
    {rest es' : List AInstr} (hi : isConstInstr i = true)
    (hc : ∀ a ∈ rest, ConstInstr a) (h : atInstr s f vs (.plain i) rest = .step s' f' es') :
    s' = s ∧ f' = f ∧ ∀ a ∈ es', ConstInstr a := by
  cases i <;> simp only [isConstInstr, Bool.false_eq_true] at hi
  case iconst w n => simp only [atInstr, instrStep, reduceCtorEq] at h
  case fconst w n => simp only [atInstr, instrStep, reduceCtorEq] at h
  case refNull t => simp only [atInstr, instrStep, reduceCtorEq] at h
  case refFunc x =>
    simp only [atInstr, instrStep] at h
    cases hg : f.inst.funcs[x]? <;>
      simp only [hg, Option.map_none, Option.map_some, reduceCtorEq, Out.step.injEq] at h
    rename_i a
    rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    intro e he
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (he | rfl) | he
    · exact constInstr_vals _ _ he
    · trivial
    · exact hc e he
  case globalGet x =>
    simp only [atInstr, instrStep] at h
    cases ha : f.inst.globals[x]? <;> simp only [ha, reduceCtorEq] at h
    rename_i a
    cases hg : s.globals[a]? <;>
      simp only [hg, Option.map_none, Option.map_some, reduceCtorEq, Out.step.injEq] at h
    rename_i g
    rcases h with ⟨rfl, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    intro e he
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (he | rfl) | he
    · exact constInstr_vals _ _ he
    · exact constInstr_val _
    · exact hc e he

theorem seq_const {s s' : Store} {f f' : Frame} {vs : List Val}
    {es es' : List AInstr} (hc : ∀ a ∈ es, ConstInstr a)
    (h : seq s f vs es = .step s' f' es') :
    s' = s ∧ f' = f ∧ ∀ a ∈ es', ConstInstr a := by
  induction es generalizing vs with
  | nil => simp only [seq, reduceCtorEq] at h
  | cons e es ih =>
    have he := hc e (by simp)
    have hrest : ∀ a ∈ es, ConstInstr a := fun a ha => hc a (by simp [ha])
    cases hv : toVal e with
    | some v =>
      simp only [seq, hv] at h
      exact ih hrest h
    | none =>
      simp only [seq, hv] at h
      cases e with
      | plain i => exact atInstr_const he hrest h
      | refFuncAddr a => simp only [toVal, reduceCtorEq] at hv
      | refExternAddr a => simp only [toVal, reduceCtorEq] at hv
      | _ => contradiction

theorem run_const {fuel : Nat} {c c' : Config} (hc : ∀ a ∈ c.instrs, ConstInstr a)
    (h : run fuel c = some c') : c'.store = c.store ∧ c'.frame = c.frame := by
  induction fuel generalizing c with
  | zero => simp only [run, reduceCtorEq] at h
  | succ fuel ih =>
    simp only [run] at h
    split at h
    · rename_i s f es hs
      rcases seq_const hc hs with ⟨rfl, rfl, hc'⟩
      exact ih (c := ⟨c.store, c.frame, es⟩) hc' h
    · cases h
      exact ⟨rfl, rfl⟩
    · contradiction

theorem step_frame_shape {H : HostSem} {c c' : Config} (h : Step H c c') :
    c'.frame.inst = c.frame.inst ∧ c'.frame.locals.length = c.frame.locals.length := by
  induction h <;> simp_all

theorem steps_frame_shape {H : HostSem} {c c' : Config} (h : Steps H c c') :
    c'.frame.inst = c.frame.inst ∧ c'.frame.locals.length = c.frame.locals.length := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail h hs ih =>
    rcases step_frame_shape hs with ⟨hi, hl⟩
    exact ⟨hi.trans ih.1, hl.trans ih.2⟩

theorem forall₂_mapM {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨y, hy, ys', hys, he⟩
    cases he
    exact .cons hy (ih hys)

theorem evalConst_sound {H : HostSem} {fuel : Nat} {s : Store} {inst : ModuleInst} {e : Expr}
    {v : Val} (h : evalConst fuel s inst e = some v) :
    Steps H ⟨s, ⟨[], inst⟩, e.map .plain⟩ ⟨s, ⟨[], inst⟩, [v.instr]⟩ := by
  cases he : e.all isConstInstr <;>
    simp only [evalConst, he, Bool.not_true, Bool.not_false, Bool.cond_false,
      Bool.cond_true, reduceCtorEq] at h
  cases hr : run fuel ⟨s, ⟨[], inst⟩, e.map .plain⟩ <;>
    simp only [hr, reduceCtorEq] at h
  rename_i c
  split at h
  · rename_i a ha
    have hv := eq_instr_of_toVal h
    have hconst : ∀ a ∈ e.map AInstr.plain, ConstInstr a := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      exact List.all_eq_true.mp he i hi
    rcases run_const hconst hr with ⟨hs, hf⟩
    have hc : c = ⟨s, ⟨[], inst⟩, [v.instr]⟩ := by
      cases c
      simp_all
    exact hc ▸ (run_sound (H := H) hr).1
  · contradiction

theorem instantiate_sound {H : HostSem} {fuel : Nat} {s s' : Store} {m : Module}
    {imports : List ExternVal} {inst : ModuleInst} (hm : ImportsMatch s m imports)
    (h : instantiate fuel s m imports = some (s', inst)) :
    Instantiated H m s imports s' inst := by
  simp only [instantiate, bind, Option.bind_eq_some_iff] at h
  rcases h with ⟨gvals, _, erefs, _, gvals₁, hg, erefs₁, he, u, hu, c, hr, hc⟩
  cases u
  simp only [guard] at hu
  split at hu
  · rename_i heq
    simp only [Bool.and_eq_true, beq_iff_eq] at heq
    rcases heq with ⟨hgv, her⟩
    subst gvals₁ erefs₁
    rcases c with ⟨sf, ff, es⟩
    cases es with
    | nil =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      refine ⟨hm, gvals, erefs, (allocModule s m imports gvals erefs).1, rfl, ?_, ?_, ?_⟩
      · apply (forall₂_mapM hg).imp
        intro g v hv
        exact evalConst_sound hv
      · apply (forall₂_mapM he).imp
        intro e rs hers
        apply (forall₂_mapM hers).imp
        intro ex r hex
        simp only [Option.bind_eq_some_iff] at hex
        rcases hex with ⟨v, hv, hvr⟩
        cases v <;> simp only [asRef, reduceCtorEq, Option.some.injEq] at hvr
        subst r
        exact evalConst_sound hv
      · have hs := (run_sound (H := H) hr).1
        rcases steps_frame_shape hs with ⟨hi, hl⟩
        have hloc : ff.locals = [] := by simpa using hl
        have hf : ff = ⟨[], (allocModule s m imports gvals erefs).2⟩ := by
          cases ff
          simp_all
        simpa only [hf] using hs
    | cons e es => contradiction
  · contradiction

end FVA.Wasm.Exec.Ref
