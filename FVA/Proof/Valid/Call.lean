import FVA.Proof.Valid.Branch

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- One type per local slot; bridges compressed declarations to runtime frame typing. -/
def localTypes (ls : List (Nat × ValType)) : List ValType :=
  ls.flatMap fun (n, t) => List.replicate n t

theorem localTypes_append (xs ys : List (Nat × ValType)) :
    localTypes (xs ++ ys) = localTypes xs ++ localTypes ys := List.flatMap_append

theorem localTypes_singletons (ts : List ValType) : localTypes (ts.map (1, ·)) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa only [localTypes, List.map_cons, List.flatMap_cons,
      List.replicate_one, List.singleton_append] using congrArg (t :: ·) ih

theorem localAt_runs (ls : List (Nat × ValType)) (x : Nat) :
    localAt ls x = (localTypes ls)[x]? := by
  induction ls generalizing x with
  | nil => rfl
  | cons nt ls ih =>
    obtain ⟨n, t⟩ := nt
    simp only [localAt, localTypes, List.flatMap_cons, List.getElem?_append,
      List.length_replicate, List.getElem?_replicate]
    split <;> simp_all only [localTypes]

theorem localAt_normalize (ls : List (Nat × ValType)) (x : Nat) :
    localAt ls x = localAt ((localTypes ls).map (1, ·)) x :=
  (localAt_runs ls x).trans (localAt_singletons (localTypes ls) x).symm

theorem default_typed (s : Store) (t : ValType) : t.default.HasType s t := by
  cases t with
  | num n => cases n <;> trivial
  | ref r => rfl

theorem localDefaults_typed (s : Store) (code : Func) :
    List.Forall₂ (Val.HasType s) code.localDefaults (localTypes code.locals) := by
  unfold Func.localDefaults localTypes
  induction code.locals with
  | nil => exact .nil
  | cons nt rest ih =>
    obtain ⟨n, t⟩ := nt
    apply List.rel_append _ ih
    induction n with
    | zero => exact .nil
    | succ n ih => exact .cons (default_typed s t) ih

theorem ASeqT.invoke_inv {s : Store} {C : Context} {addr : Nat} {fi : FuncInst}
    {vs : List Val} {a b : List OpType}
    (h : ASeqT s C (vals vs ++ [.invoke addr]) ⟨a, b⟩)
    (hfi : s.funcs[addr]? = some fi) (hlen : vs.length = fi.type.params.length) :
    ∃ p, Matches a p ∧ Matches (p ++ ops fi.type.results) b ∧
      List.Forall₂ (Val.HasType s) vs fi.type.params := by
  obtain ⟨p, x, y, hp, hout, hi, hvs⟩ := h.fixed_arity_inv (by
    intro x y hi
    cases hi with | invoke hlookup =>
      have heq := Option.some.inj (hlookup.symm.trans hfi)
      cases heq
      simpa only [ops, List.length_map] using hlen)
  cases hi with | invoke hlookup =>
    have heq := Option.some.inj (hlookup.symm.trans hfi)
    cases heq
    exact ⟨p, hp, hout, hasOp_ops_iff.mp hvs⟩

theorem wasm_frame_typed {s : Store} {C D : Context} {inst : ModuleInst} {code : Func}
    {ft : FuncType} {vs : List Val} (hi : ModuleInstT s inst C) (hc : FuncT C code ft)
    (hvs : List.Forall₂ (Val.HasType s) vs ft.params) :
    AInstrT s D (.frame ft.results.length ⟨vs ++ code.localDefaults, inst⟩
      [.label ft.results.length [] (code.body.map .plain)]) ⟨[], ops ft.results⟩ := by
  let ts := localTypes (ft.params.map (1, ·) ++ code.locals)
  let FC : Context := { C with locals := ts.map (1, ·) }
  have hlocals : List.Forall₂ (Val.HasType s) (vs ++ code.localDefaults) ts := by
    simpa only [ts, localTypes_append, localTypes_singletons] using
      List.rel_append hvs (localDefaults_typed s code)
  have hf : FrameT s ⟨vs ++ code.localDefaults, inst⟩ FC := ⟨C, ts, hi, hlocals, rfl⟩
  have he : Context.Entails
      { C with
        locals := ft.params.map (1, ·) ++ code.locals
        labels := [ft.results]
        return_ := some ft.results }
      ({ FC with return_ := some ft.results }.withLabel ft.results) := by
    refine ⟨rfl, rfl, fun _ tt ht => ⟨tt, ht, rfl⟩, fun _ lim hm => ⟨lim, hm⟩,
      rfl, rfl, Nat.le_refl _, ?_, ?_, rfl, fun _ hx => hx⟩
    · exact localAt_normalize _
    · exact congrArg (ft.results :: ·) hi.noLabels.symm
  obtain ⟨out, hbody, hm⟩ := hc.2
  exact .frame rfl hf (.single (.label rfl .nil (ASeqT.plain (.sub (hbody.transport he) hm))))

theorem ASeqT.invoke {s : Store} {C : Context} {addr : Nat} {ft : FuncType}
    {inst : ModuleInst} {code : Func} {vs : List Val} {a b : List OpType}
    (hok : StoreOK s) (h : ASeqT s C (vals vs ++ [.invoke addr]) ⟨a, b⟩)
    (hfi : s.funcs[addr]? = some (.wasm ft inst code)) (hlen : vs.length = ft.params.length) :
    ASeqT s C [.frame ft.results.length ⟨vs ++ code.localDefaults, inst⟩
      [.label ft.results.length [] (code.body.map .plain)]] ⟨a, b⟩ := by
  obtain ⟨p, hp, hout, hvs⟩ := h.invoke_inv hfi hlen
  obtain ⟨D, hi, hc⟩ := hok.funcs _ (List.mem_of_getElem? hfi)
  have hnew := ASeqT.single (wasm_frame_typed (D := C) hi hc hvs)
  have framed := hnew.frame p
  simp only [List.append_nil] at framed
  exact .sub (framed.input hp) hout

end FVA.Wasm.Valid
