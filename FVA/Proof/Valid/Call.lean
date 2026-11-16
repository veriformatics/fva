import FVA.Proof.Valid.Branch
import FVA.Proof.Valid.Closed

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- One entry per local slot; bridges compressed declarations to runtime frame typing. -/
def localTypes {α : Type} (ls : List (Nat × α)) : List α :=
  ls.flatMap fun (n, t) => List.replicate n t

theorem localTypes_append {α : Type} (xs ys : List (Nat × α)) :
    localTypes (xs ++ ys) = localTypes xs ++ localTypes ys := List.flatMap_append

theorem localTypes_singletons {α : Type} (ts : List α) : localTypes (ts.map (1, ·)) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa only [localTypes, List.map_cons, List.flatMap_cons,
      List.replicate_one, List.singleton_append] using congrArg (t :: ·) ih

theorem localAt_runs (ls : List (Nat × LocalType)) (x : Nat) :
    localAt ls x = (localTypes ls)[x]? := by
  induction ls generalizing x with
  | nil => rfl
  | cons nt ls ih =>
    obtain ⟨n, t⟩ := nt
    simp only [localAt, localTypes, List.flatMap_cons, List.getElem?_append,
      List.length_replicate, List.getElem?_replicate]
    split <;> simp_all only [localTypes]

theorem localAt_normalize (ls : List (Nat × LocalType)) (x : Nat) :
    localAt ls x = localAt ((localTypes ls).map (1, ·)) x :=
  (localAt_runs ls x).trans (localAt_singletons (localTypes ls) x).symm

theorem default_mapHeap (σ : HeapType → HeapType) (t : ValType) :
    (t.mapHeap σ).default = t.default := by
  cases t with
  | num n => rfl
  | ref r => rfl

theorem defaultable_mapHeap (σ : HeapType → HeapType) (t : ValType) :
    (t.mapHeap σ).defaultable = t.defaultable := by
  cases t <;> rfl

theorem default_local {s : Store} {t : ValType} (hc : t.Closed 0) :
    LocalOK s t.default ⟨t.defaultable, t⟩ := by
  cases t with
  | num n => cases n <;> exact ⟨rfl, hc, trivial⟩
  | ref r =>
    obtain ⟨null, heap⟩ := r
    cases null with
    | true => exact ⟨rfl, hc, rfl⟩
    | false => exact ⟨rfl, hc⟩

/-- The declared locals' defaults are typed at their closed types, set exactly when
defaultable. -/
theorem localDefaults_typed (s : Store) (C : Context) (code : Func)
    (hd : ∀ d ∈ C.types, d.Closed) (hs : ∀ l ∈ code.locals, l.2.Src C.types.length) :
    List.Forall₂ (LocalOK s) code.localDefaults
      (localTypes (code.locals.map fun l =>
        (l.1, (⟨l.2.defaultable, C.close l.2⟩ : LocalType)))) := by
  unfold Func.localDefaults localTypes
  generalize code.locals = ls at hs ⊢
  induction ls with
  | nil => exact .nil
  | cons nt rest ih =>
    obtain ⟨n, t⟩ := nt
    simp only [List.flatMap_cons, List.map_cons]
    apply List.rel_append _ (ih fun l hl => hs l (by simp [hl]))
    have ht : t.Src C.types.length := hs (n, t) (by simp)
    have hcl : (C.close t).Closed 0 := ValType.closed_close hd ht
    have hl := default_local (s := s) hcl
    simp only [Context.close, default_mapHeap, defaultable_mapHeap] at hl
    clear hs ih
    induction n with
    | zero => exact .nil
    | succ n ih => exact .cons hl ih

theorem ASeqT.invoke_inv {s : Store} {C : Context} {addr : Nat} {fi : FuncInst} {ft : FuncType}
    {vs : List Val} {a b : List OpType}
    (h : ASeqT s C (vals vs ++ [.invoke addr]) ⟨a, b⟩)
    (hfi : s.funcs[addr]? = some fi) (hft : fi.type.expand = some ft)
    (hlen : vs.length = ft.params.length) :
    ∃ p, Matches a p ∧ Matches (p ++ ops ft.results) b ∧
      List.Forall₂ (Val.HasType s) vs ft.params := by
  obtain ⟨p, x, y, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (by
    intro x y hi
    cases hi with | invoke hlookup hft' =>
      have heq := Option.some.inj (hlookup.symm.trans hfi)
      cases heq
      obtain rfl : ft = _ := Option.some.inj (hft.symm.trans hft')
      simpa only [ops, List.length_map] using hlen)
  cases hi with | invoke hlookup hft' =>
    have heq := Option.some.inj (hlookup.symm.trans hfi)
    cases heq
    obtain rfl : ft = _ := Option.some.inj (hft.symm.trans hft')
    exact ⟨p, hp, hout, hasOp_ops_iff.mp hvs⟩

theorem localTypes_ones {α β : Type} (f : β → α) (ts : List β) :
    localTypes (ts.map fun x => (1, f x)) = ts.map f := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa only [localTypes, List.map_cons, List.flatMap_cons,
      List.replicate_one, List.singleton_append] using congrArg (f t :: ·) ih

theorem params_local {s : Store} {vs : List Val} {ts : List ValType}
    (h : List.Forall₂ (Val.HasType s) vs ts) (hc : ∀ t ∈ ts, t.Closed 0) :
    List.Forall₂ (LocalOK s) (vs.map some) (ts.map (⟨true, ·⟩)) := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih =>
    exact .cons ⟨rfl, hc _ (by simp), hv⟩ (ih fun t ht => hc t (by simp [ht]))

theorem wasm_frame_typed {s : Store} {C D : Context} {inst : ModuleInst} {code : Func}
    {dt : DefType} {ft : FuncType} {vs : List Val} (hi : ModuleInstT s inst C)
    (hc : FuncT C code dt) (hdt : dt.Closed) (hft : dt.expand = some ft)
    (hvs : List.Forall₂ (Val.HasType s) vs ft.params) :
    AInstrT s D (.frame ft.results.length ⟨vs.map some ++ code.localDefaults, inst⟩
      [.label ft.results.length [] (code.body.map .plain)]) ⟨[], ops ft.results⟩ := by
  obtain ⟨hty, ft', hft', hsrc, out, hbody, hm⟩ := hc
  have hfe : ft = ft' := Option.some.inj (hft.symm.trans hft')
  subst hfe
  obtain ⟨f₀, hf₀, hcl⟩ := DefType.expand_closed hdt
  have hf0 : ft = f₀ := Option.some.inj (hft.symm.trans hf₀)
  subst hf0
  have hd : ∀ d ∈ C.types, d.Closed := by rw [hi.types]; exact hi.typesOk
  let L : List (Nat × LocalType) := ft.params.map (1, ⟨true, ·⟩) ++
    code.locals.map fun l => (l.1, ⟨l.2.defaultable, C.close l.2⟩)
  let FC : Context := { C with locals := (localTypes L).map (1, ·) }
  have hparams := params_local hvs (FuncType.closed_iff.mp hcl).1
  have hlocals : List.Forall₂ (LocalOK s) (vs.map some ++ code.localDefaults) (localTypes L) := by
    have := List.rel_append hparams (localDefaults_typed s C code hd hsrc)
    simpa only [L, localTypes_append, localTypes_ones] using this
  have hf : FrameT s ⟨vs.map some ++ code.localDefaults, inst⟩ FC :=
    ⟨C, localTypes L, hi, hlocals, rfl⟩
  have he : Context.Entails
      { C with locals := L, labels := [ft.results], return_ := some ft.results }
      ({ FC with return_ := some ft.results }.withLabel ft.results) := by
    refine ⟨rfl, rfl, rfl, fun _ tt ht => ⟨tt, ht, rfl⟩, fun _ lim hm => ⟨lim, hm⟩,
      rfl, rfl, Nat.le_refl _, ?_, ?_, rfl, fun _ hx => hx, id⟩
    · intro x lt hx
      refine ⟨lt, ?_, rfl, fun hr => .inl (by simpa [hi.noSets, hi.noDead] using hr)⟩
      show localAt ((localTypes L).map (1, ·)) x = some lt
      rw [← localAt_normalize]; exact hx
    · exact congrArg (ft.results :: ·) hi.noLabels.symm
  exact .frame rfl hf (.single (.label rfl .nil (ASeqT.plain (.sub (hbody.transport he) hm))))

theorem ASeqT.invoke {s : Store} {C : Context} {addr : Nat} {dt : DefType} {ft : FuncType}
    {inst : ModuleInst} {code : Func} {vs : List Val} {a b : List OpType}
    (hok : StoreOK s) (h : ASeqT s C (vals vs ++ [.invoke addr]) ⟨a, b⟩)
    (hfi : s.funcs[addr]? = some (.wasm dt inst code)) (hft : dt.expand = some ft)
    (hlen : vs.length = ft.params.length) :
    ASeqT s C [.frame ft.results.length ⟨vs.map some ++ code.localDefaults, inst⟩
      [.label ft.results.length [] (code.body.map .plain)]] ⟨a, b⟩ := by
  obtain ⟨p, hp, hout, hvs⟩ := h.invoke_inv hfi hft hlen
  obtain ⟨hdt, D, hi, hc⟩ := hok.funcs _ (List.mem_of_getElem? hfi)
  have hnew := ASeqT.single (wasm_frame_typed (D := C) hi hc hdt hft hvs)
  have framed := hnew.frame p
  simp only [List.append_nil] at framed
  exact .sub (framed.input hp) hout

end FVA.Wasm.Valid
