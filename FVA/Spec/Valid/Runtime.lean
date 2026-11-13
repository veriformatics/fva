import FVA.Spec.Valid.Module
import FVA.Spec.Exec.Host

/-!
# Runtime typing (reviewed spec; contracts U6 T3, T4, U28c V6–V7)

Transcribes WebAssembly 3.0 SpecTec `859d3232` `7.1` (soundness: administrative instructions,
instances, store, frames, configurations) and `4.1` (`Ref_ok`) for FVA's runtime: store validity
with every declared type closed, module instances classified by closed contexts (tables and
memories by their current limits), frames with each local's initialization state,
administrative instructions (labels, frames, exception handlers, tail calls, reference values)
and configurations. FVA keeps values on the instruction sequence (`Val.instr`), so a thread's
sequence has type `[] → [t*]`. Hosts: a host call from a valid store must yield a valid store;
store extension does not imply it, so `TypeSoundHost` adds that requirement to `ValidHost`.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- `S ⊢ externval : externtype` (appendix "External Values"): the address names an instance. -/
def ExternValT (s : Store) : ExternVal → Prop
  | .func a => a < s.funcs.length
  | .table a => a < s.tables.length
  | .mem a => a < s.mems.length
  | .global a => a < s.globals.length
  | .tag a => a < s.tags.length

/-- `S ⊢ moduleinst : C` (3.0 `Moduleinst_ok`): the context's types are the instance's closed
defined types; each address names an instance of the context's type (a function or tag by its
defined type, a table or memory by its current limits, a global by global type matching), the
data segments exist, the exports name instances under distinct names; `C.refs` = every function
index; no locals, initializations, labels or return type. -/
structure ModuleInstT (s : Store) (inst : ModuleInst) (C : Context) : Prop where
  types : C.types = inst.types
  typesOk : ∀ d ∈ inst.types, d.Closed
  tags : List.Forall₂ (fun a dt => ∃ ti, s.tags[a]? = some ti ∧ ti.type = dt) inst.tags C.tags
  funcs : List.Forall₂ (fun a dt => ∃ fi, s.funcs[a]? = some fi ∧ fi.type = dt) inst.funcs
    C.funcs
  tables : List.Forall₂ (fun a tt => ∃ ti, s.tables[a]? = some ti ∧ ti.type = tt) inst.tables
    C.tables
  mems : List.Forall₂
    (fun a lim => ∃ mi, s.mems[a]? = some mi ∧ (⟨mi.pages, mi.max⟩ : Limits) = lim)
    inst.mems C.mems
  /-- Globals by global type matching (an immutable global of a subtype serves). -/
  globals : List.Forall₂ (fun a gt => ∃ gi, s.globals[a]? = some gi ∧ gi.type.Sub gt)
    inst.globals C.globals
  elems : List.Forall₂ (fun a rt => ∃ ei, s.elems[a]? = some ei ∧ ei.type = rt) inst.elems C.elems
  datas : C.datas = inst.datas.length ∧ ∀ a ∈ inst.datas, a < s.datas.length
  exports : ∀ ex ∈ inst.exports, ExternValT s ex.value
  exportNames : (inst.exports.map (·.name)).Nodup
  refs : C.refs = List.range inst.funcs.length
  noLocals : C.locals = []
  noSets : C.sets = []
  noDead : C.dead = false
  noLabels : C.labels = []
  noReturn : C.return_ = none

/-- `S ⊢ funcinst : dt` (3.0 `Funcinst_ok`): a closed well-formed defined type; module code is
typed in its instance's context; a host function's behavior is constrained by
`TypeSoundHost`. -/
def FuncInstOK (s : Store) : FuncInst → Prop
  | .wasm dt inst code => dt.Closed ∧ ∃ C, ModuleInstT s inst C ∧ FuncT C code dt
  | .host dt _ => dt.Closed

/-- `⊢ store ok` (3.0 `Store_ok`; exception acyclicity omitted, contract X3): every instance's
declared type closed and well-formed, whatever it holds. -/
structure StoreOK (s : Store) : Prop where
  /-- Tags: function types without results. -/
  tags : ∀ ti ∈ s.tags, ti.type.Closed ∧ ∃ ts, ti.type.expand = some ⟨ts, []⟩
  funcs : ∀ fi ∈ s.funcs, FuncInstOK s fi
  /-- Tables: valid limits, a closed element type, as many elements as the minimum (it tracks
  the size), each of the element type. -/
  tables : ∀ ti ∈ s.tables, ti.type.Ok ∧ (ValType.ref ti.type.elem).Closed 0 ∧
    ti.elem.length = ti.type.limits.min ∧ ∀ r ∈ ti.elem, Val.HasType s (.ref r) (.ref ti.type.elem)
  /-- Memories: valid limits (the size is `pages · 65536` by representation). -/
  mems : ∀ mi ∈ s.mems, memTypeOk ⟨mi.pages, mi.max⟩
  globals : ∀ gi ∈ s.globals, gi.type.val.Closed 0 ∧ Val.HasType s gi.value gi.type.val
  elems : ∀ ei ∈ s.elems, (ValType.ref ei.type).Closed 0 ∧
    ∀ r ∈ ei.elem, Val.HasType s (.ref r) (.ref ei.type)
  /-- Exceptions: an existing tag, the fields typed by its parameters (`Exninst_ok`). -/
  exns : ∀ e ∈ s.exns, ∃ ti ts, s.tags[e.tag]? = some ti ∧ ti.type.expand = some ⟨ts, []⟩ ∧
    List.Forall₂ (Val.HasType s) e.fields ts

/-- `S ⊢ val? : lt` (3.0 `Localval_ok`): a set local holds a value of its type, an unset one
none; the type closed. -/
def LocalOK (s : Store) : Option Val → LocalType → Prop
  | some v, lt => lt.set = true ∧ lt.type.Closed 0 ∧ Val.HasType s v lt.type
  | none, lt => lt.set = false ∧ lt.type.Closed 0

/-- `S ⊢ frame : C` (3.0 `Frame_ok`): the instance's context with the locals' types and
states, one run per local. -/
def FrameT (s : Store) (f : Frame) (C : Context) : Prop :=
  ∃ C₀ lts, ModuleInstT s f.inst C₀ ∧ List.Forall₂ (LocalOK s) f.locals lts ∧
    C = { C₀ with locals := lts.map (1, ·) }

/-- The locals an administrative instruction initializes for the rest of its sequence: a plain
instruction's (`Instr.sets`), nothing for the others. -/
def _root_.FVA.Wasm.Exec.AInstr.sets : AInstr → List Nat
  | .plain i => i.sets
  | _ => []

/-- An instruction after which its sequence never continues: `trap`, `throw_ref` (it throws or
traps). -/
def _root_.FVA.Wasm.Exec.AInstr.dead : AInstr → Bool
  | .trap | .plain .throwRef => true
  | _ => false

/-- The context an instruction after `es` is typed in (runtime `Instrs_ok2/seq`): `es`'s
initializations added, and every local readable once `es` holds a dead end (contract X9: a
`trap` or `throw_ref` reduced inside a subsequence leaves a tail that never runs but whose reads
the initializations it skipped no longer cover). -/
def Context.after (C : Context) (es : List AInstr) : Context :=
  { C.addSets (es.flatMap AInstr.sets) with dead := C.dead || es.any AInstr.dead }

mutual

/-- `S; C ⊢ admininstr : [t₁*] → [t₂*]` (3.0 `Instr_ok2`); plain instructions by `InstrT`. A
frame's body is a thread under the frame's return type. -/
inductive AInstrT (s : Store) : Context → AInstr → StackType → Prop where
  | plain {C : Context} {i : Instr} {st : StackType} (h : InstrT C i st) :
      AInstrT s C (.plain i) st
  | refFuncAddr {C : Context} {a : Nat} {fi : FuncInst} (h : s.funcs[a]? = some fi) :
      AInstrT s C (.refFuncAddr a) ⟨[], [.val (.ref ⟨false, .def_ fi.type⟩)]⟩
  | refExternAddr {C : Context} {a : Nat} :
      AInstrT s C (.refExternAddr a) ⟨[], [.val (.ref ⟨false, .abs .extern⟩)]⟩
  | refNullAddr {C : Context} {ht : HeapType} :
      AInstrT s C .refNullAddr ⟨[], [.val (.ref ⟨true, ht⟩)]⟩
  | refExnAddr {C : Context} {a : Nat} (h : a < s.exns.length) :
      AInstrT s C (.refExnAddr a) ⟨[], [.val (.ref ⟨false, .abs .exn⟩)]⟩
  | trap {C : Context} {t₁ t₂ : List OpType} : AInstrT s C .trap ⟨t₁, t₂⟩
  | invoke {C : Context} {a : Nat} {fi : FuncInst} {ft : FuncType} (h : s.funcs[a]? = some fi)
      (hft : fi.type.expand = some ft) :
      AInstrT s C (.invoke a) ⟨ops ft.params, ops ft.results⟩
  | label {C : Context} {n : Nat} {cont : List Instr} {body : List AInstr}
      {t₁ t₂ : List ValType} (hn : t₁.length = n) (hc : SeqT C cont ⟨ops t₁, ops t₂⟩)
      (hb : ASeqT s (C.withLabel t₁) body ⟨[], ops t₂⟩) :
      AInstrT s C (.label n cont body) ⟨[], ops t₂⟩
  | frame {C C' : Context} {n : Nat} {f : Frame} {body : List AInstr} {ts : List ValType}
      (hn : ts.length = n) (hf : FrameT s f C')
      (hb : ASeqT s { C' with return_ := some ts } body ⟨[], ops ts⟩) :
      AInstrT s C (.frame n f body) ⟨[], ops ts⟩
  | handler {C : Context} {n : Nat} {cs : List Catch} {body : List AInstr} {ts : List ValType}
      (hc : ∀ c ∈ cs, CatchOK C c) (hb : ASeqT s C body ⟨[], ops ts⟩) :
      AInstrT s C (.handler n cs body) ⟨[], ops ts⟩
  | returnInvoke {C : Context} {a : Nat} {fi : FuncInst} {ft : FuncType} {rs : List ValType}
      {t₃ t₄ : List OpType} (h : s.funcs[a]? = some fi) (hft : fi.type.expand = some ft)
      (hr : C.return_ = some rs) (hs : ResultSub ft.results rs) :
      AInstrT s C (.returnInvoke a) ⟨t₃ ++ ops ft.params, t₄⟩

/-- Sequences of administrative instructions, composed as `SeqT` does (incl. `sub`). -/
inductive ASeqT (s : Store) : Context → List AInstr → StackType → Prop where
  | nil {C : Context} {ts : List OpType} : ASeqT s C [] ⟨ts, ts⟩
  | snoc {C : Context} {es : List AInstr} {e : AInstr} {t₁ t₀ t' t t₃ : List OpType}
      (hs : ASeqT s C es ⟨t₁, t₀ ++ t'⟩) (hm : Matches t' t)
      (he : AInstrT s (C.after es) e ⟨t, t₃⟩) :
      ASeqT s C (es ++ [e]) ⟨t₁, t₀ ++ t₃⟩
  | sub {C : Context} {es : List AInstr} {t₁ t₂ t₂' : List OpType} (hs : ASeqT s C es ⟨t₁, t₂⟩)
      (hm : Matches t₂ t₂') : ASeqT s C es ⟨t₁, t₂'⟩

end

/-- `⊢ S; T : [t*]` (3.0 `Config_ok`): a valid store, and the thread typed under its frame's
context, which has no labels and no return type (a free `br` or `return` is ill-typed). -/
def ConfigOK (c : Config) (ts : List ValType) : Prop :=
  StoreOK c.store ∧ ∃ C, FrameT c.store c.frame C ∧ ASeqT c.store C c.instrs ⟨[], ops ts⟩

/-- Every outcome of a well-typed host call from a valid store has a valid store; divergence
needs nothing (appendix "Host Function Instances"). -/
def HostPreservesStore (H : HostSem) : Prop :=
  ∀ (s : Store) (a : Nat) (dt : DefType) (ft : FuncType) (id : Nat) (args : List Val)
    (o : HostOutcome),
    StoreOK s → s.funcs[a]? = some (.host dt id) → dt.expand = some ft →
      List.Forall₂ (Val.HasType s) args ft.params →
      H id s args o →
        match o with
        | .returned s' _ => StoreOK s'
        | .trapped s' => StoreOK s'
        | .diverged => True

/-- What type soundness asks of hosts: `ValidHost` (an outcome exists; outcomes extend the store
and return typed results) and valid stores stay valid. -/
def TypeSoundHost (H : HostSem) : Prop := ValidHost H ∧ HostPreservesStore H

end FVA.Wasm.Valid
