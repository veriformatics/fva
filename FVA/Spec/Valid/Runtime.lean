import FVA.Spec.Valid.Module
import FVA.Spec.Exec.Host

/-!
# Runtime typing (reviewed spec; contract U6 T3, T4)

Transcribes the WebAssembly 2.0 appendix "Soundness" for FVA's runtime: store validity, module
instances classified by contexts (tables and memories by their current limits), frames,
administrative instructions, threads and configurations. FVA keeps values on the instruction
sequence (`Val.instr`), so a thread's sequence has type `[] → [t*]` as in the appendix. Hosts:
the appendix asks that a host call from a valid store yields a valid store; store extension does
not imply it, so `TypeSoundHost` adds that requirement to `ValidHost`.
-/

namespace FVA.Wasm.Valid

open FVA.Wasm FVA.Wasm.Exec

/-- `S ⊢ externval : externtype` (appendix "External Values"): the address names an instance. -/
def ExternValT (s : Store) : ExternVal → Prop
  | .func a => a < s.funcs.length
  | .table a => a < s.tables.length
  | .mem a => a < s.mems.length
  | .global a => a < s.globals.length

/-- `S ⊢ moduleinst : C` (appendix "Module Instances"): each address names an instance of the
context's type (a table or memory by its current limits), the data segments exist, the exports
name instances under distinct names; `C.refs` = every function index; no locals, labels or
return type. -/
structure ModuleInstT (s : Store) (inst : ModuleInst) (C : Context) : Prop where
  types : C.types = inst.types
  funcs : List.Forall₂ (fun a ft => ∃ fi, s.funcs[a]? = some fi ∧ fi.type = ft) inst.funcs C.funcs
  tables : List.Forall₂ (fun a tt => ∃ ti, s.tables[a]? = some ti ∧ ti.type = tt) inst.tables
    C.tables
  mems : List.Forall₂
    (fun a lim => ∃ mi, s.mems[a]? = some mi ∧ (⟨mi.pages, mi.max⟩ : Limits) = lim)
    inst.mems C.mems
  globals : List.Forall₂ (fun a gt => ∃ gi, s.globals[a]? = some gi ∧ gi.type = gt) inst.globals
    C.globals
  elems : List.Forall₂ (fun a rt => ∃ ei, s.elems[a]? = some ei ∧ ei.type = rt) inst.elems C.elems
  datas : C.datas = inst.datas.length ∧ ∀ a ∈ inst.datas, a < s.datas.length
  exports : ∀ ex ∈ inst.exports, ExternValT s ex.value
  exportNames : (inst.exports.map (·.name)).Nodup
  refs : C.refs = List.range inst.funcs.length
  noLocals : C.locals = []
  noLabels : C.labels = []
  noReturn : C.return_ = none

/-- `S ⊢ funcinst : functype` (appendix "Function Instances"): module code is typed in its
instance's context; a host function's behavior is constrained by `TypeSoundHost`. -/
def FuncInstOK (s : Store) : FuncInst → Prop
  | .wasm ft inst code => ∃ C, ModuleInstT s inst C ∧ FuncT C code ft
  | .host _ _ => True

/-- `⊢ store ok` (appendix "Store Validity"). -/
structure StoreOK (s : Store) : Prop where
  funcs : ∀ fi ∈ s.funcs, FuncInstOK s fi
  /-- Tables: valid limits, as many elements as the minimum (it tracks the size), each of the
  element type. -/
  tables : ∀ ti ∈ s.tables, ti.type.Ok ∧ ti.elem.length = ti.type.limits.min ∧
    ∀ r ∈ ti.elem, Val.HasType s (.ref r) (.ref ti.type.elem)
  /-- Memories: valid limits (the size is `pages · 65536` by representation). -/
  mems : ∀ mi ∈ s.mems, memTypeOk ⟨mi.pages, mi.max⟩
  globals : ∀ gi ∈ s.globals, Val.HasType s gi.value gi.type.val
  elems : ∀ ei ∈ s.elems, ∀ r ∈ ei.elem, Val.HasType s (.ref r) (.ref ei.type)

/-- `S ⊢ frame : C` (appendix "Frames"): the instance's context with the locals' types, one run
per local. -/
def FrameT (s : Store) (f : Frame) (C : Context) : Prop :=
  ∃ C₀ ts, ModuleInstT s f.inst C₀ ∧ List.Forall₂ (Val.HasType s) f.locals ts ∧
    C = { C₀ with locals := ts.map (1, ·) }

mutual

/-- `S; C ⊢ admininstr : [t₁*] → [t₂*]` (appendix "Administrative Instructions"); plain
instructions by `InstrT`. A frame's body is a thread under the frame's return type. -/
inductive AInstrT (s : Store) : Context → AInstr → StackType → Prop where
  | plain {C : Context} {i : Instr} {st : StackType} (h : InstrT C i st) :
      AInstrT s C (.plain i) st
  | refFuncAddr {C : Context} {a : Nat} (h : a < s.funcs.length) :
      AInstrT s C (.refFuncAddr a) ⟨[], [.val (.ref .funcref)]⟩
  | refExternAddr {C : Context} {a : Nat} :
      AInstrT s C (.refExternAddr a) ⟨[], [.val (.ref .externref)]⟩
  | trap {C : Context} {t₁ t₂ : List OpType} : AInstrT s C .trap ⟨t₁, t₂⟩
  | invoke {C : Context} {a : Nat} {fi : FuncInst} (h : s.funcs[a]? = some fi) :
      AInstrT s C (.invoke a) ⟨ops fi.type.params, ops fi.type.results⟩
  | label {C : Context} {n : Nat} {cont : List Instr} {body : List AInstr}
      {t₁ t₂ : List ValType} (hn : t₁.length = n) (hc : SeqT C cont ⟨ops t₁, ops t₂⟩)
      (hb : ASeqT s (C.withLabel t₁) body ⟨[], ops t₂⟩) :
      AInstrT s C (.label n cont body) ⟨[], ops t₂⟩
  | frame {C C' : Context} {n : Nat} {f : Frame} {body : List AInstr} {ts : List ValType}
      (hn : ts.length = n) (hf : FrameT s f C')
      (hb : ASeqT s { C' with return_ := some ts } body ⟨[], ops ts⟩) :
      AInstrT s C (.frame n f body) ⟨[], ops ts⟩

/-- Sequences of administrative instructions, composed as `SeqT` does (incl. `sub`). -/
inductive ASeqT (s : Store) : Context → List AInstr → StackType → Prop where
  | nil {C : Context} {ts : List OpType} : ASeqT s C [] ⟨ts, ts⟩
  | snoc {C : Context} {es : List AInstr} {e : AInstr} {t₁ t₀ t' t t₃ : List OpType}
      (hs : ASeqT s C es ⟨t₁, t₀ ++ t'⟩) (hm : Matches t' t) (he : AInstrT s C e ⟨t, t₃⟩) :
      ASeqT s C (es ++ [e]) ⟨t₁, t₀ ++ t₃⟩
  | sub {C : Context} {es : List AInstr} {t₁ t₂ t₂' : List OpType} (hs : ASeqT s C es ⟨t₁, t₂⟩)
      (hm : Matches t₂ t₂') : ASeqT s C es ⟨t₁, t₂'⟩

end

/-- `⊢ S; T : [t*]` (appendix "Configurations"): a valid store, and the thread typed under its
frame's context, which has no labels and no return type (a free `br` or `return` is
ill-typed). -/
def ConfigOK (c : Config) (ts : List ValType) : Prop :=
  StoreOK c.store ∧ ∃ C, FrameT c.store c.frame C ∧ ASeqT c.store C c.instrs ⟨[], ops ts⟩

/-- Every outcome of a well-typed host call from a valid store has a valid store; divergence
needs nothing (appendix "Host Function Instances"). -/
def HostPreservesStore (H : HostSem) : Prop :=
  ∀ (s : Store) (a : Nat) (ft : FuncType) (id : Nat) (args : List Val) (o : HostOutcome),
    StoreOK s → s.funcs[a]? = some (.host ft id) → List.Forall₂ (Val.HasType s) args ft.params →
      H id s args o →
        match o with
        | .returned s' _ => StoreOK s'
        | .trapped s' => StoreOK s'
        | .diverged => True

/-- What type soundness asks of hosts: `ValidHost` (an outcome exists; outcomes extend the store
and return typed results) and valid stores stay valid. -/
def TypeSoundHost (H : HostSem) : Prop := ValidHost H ∧ HostPreservesStore H

end FVA.Wasm.Valid
