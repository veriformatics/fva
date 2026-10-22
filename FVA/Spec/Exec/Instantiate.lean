import FVA.Spec.Exec.Step
import FVA.Spec.Claims

/-!
# Allocation and instantiation (reviewed spec)

Transcribes WebAssembly 2.0 §4.5.3 (`allocmodule`) and §4.5.4 (instantiation) for FVA's
profile. `Instantiated` relates a module, a store and its imports to the store and instance of a
successful instantiation: the imports match the module's import types, allocation follows
`allocModule`, the global and element initializers evaluate (in the allocated store, as the
spec's recursive device states) to the values allocation used, and the initialization code
(active element and data segments, declarative drops, the start function) runs to completion.
A trap or divergence in that code is no successful instantiation. Module validity is the U6
premise (`docs/contracts/U4-semantics.md` S5); claims add it once U6 defines it.
-/

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- Limits subtyping (§4.5.2): `l₁` matches `l₂`. -/
def Limits.Matches (l₁ l₂ : Limits) : Prop :=
  l₂.min ≤ l₁.min ∧ ∀ m₂, l₂.max = some m₂ → ∃ m₁, l₁.max = some m₁ ∧ m₁ ≤ m₂

/-- An external value matches an import description (§4.5.2), with the module's types; a table
or memory is typed by its current size. -/
def ExternVal.Matches (s : Store) (types : List FuncType) : ExternVal → ImportDesc → Prop
  | .func a, .func x => ∃ fi ft, s.funcs[a]? = some fi ∧ types[x]? = some ft ∧ fi.type = ft
  | .table a, .table tt => ∃ t, s.tables[a]? = some t ∧
      Limits.Matches ⟨t.elem.length, t.type.limits.max⟩ tt.limits ∧ t.type.elem = tt.elem
  | .mem a, .mem lim => ∃ mi, s.mems[a]? = some mi ∧ Limits.Matches ⟨mi.pages, mi.max⟩ lim
  | .global a, .global gt => ∃ g, s.globals[a]? = some g ∧ g.type = gt
  | _, _ => False

/-- Every import is supplied by a matching external value, in order. -/
def ImportsMatch (s : Store) (m : Module) (imports : List ExternVal) : Prop :=
  List.Forall₂ (fun ev im => ev.Matches s m.types im.desc) imports m.imports

/-- The addresses of one kind among external values (`funcs(externval*)` etc.). -/
def ExternVal.funcs (evs : List ExternVal) : List Nat :=
  evs.filterMap fun | .func a => some a | _ => none
/-- See `ExternVal.funcs`. -/
def ExternVal.tables (evs : List ExternVal) : List Nat :=
  evs.filterMap fun | .table a => some a | _ => none
/-- See `ExternVal.funcs`. -/
def ExternVal.mems (evs : List ExternVal) : List Nat :=
  evs.filterMap fun | .mem a => some a | _ => none
/-- See `ExternVal.funcs`. -/
def ExternVal.globals (evs : List ExternVal) : List Nat :=
  evs.filterMap fun | .global a => some a | _ => none

/-- `allocmodule(S, module, externval_im*, val*, (ref*)*)` (§4.5.3.10): fresh addresses after
the store's current ones; the instance's index spaces start with the imports. -/
def allocModule (s : Store) (m : Module) (imports : List ExternVal) (gvals : List Val)
    (erefs : List (List Ref)) : Store × ModuleInst :=
  let fresh (base n : Nat) := (List.range n).map (base + ·)
  let funcs := ExternVal.funcs imports ++ fresh s.funcs.length m.funcs.length
  let tables := ExternVal.tables imports ++ fresh s.tables.length m.tables.length
  let mems := ExternVal.mems imports ++ fresh s.mems.length m.mems.length
  let globals := ExternVal.globals imports ++ fresh s.globals.length m.globals.length
  let exportValue : ExportDesc → ExternVal
    | .func x => .func (funcs[x]?.getD 0)
    | .table x => .table (tables[x]?.getD 0)
    | .mem x => .mem (mems[x]?.getD 0)
    | .global x => .global (globals[x]?.getD 0)
  let inst : ModuleInst :=
    { types := m.types, funcs, tables, mems, globals,
      elems := fresh s.elems.length m.elems.length,
      datas := fresh s.datas.length m.datas.length,
      exports := m.exports.map fun e => { name := e.name, value := exportValue e.desc } }
  let s' : Store :=
    { funcs := s.funcs ++ m.funcs.map fun fn => .wasm (m.types[fn.type]?.getD ⟨[], []⟩) inst fn,
      tables := s.tables ++ m.tables.map fun tt =>
        { type := tt, elem := List.replicate tt.limits.min (.null tt.elem) },
      mems := s.mems ++ m.mems.map fun lim =>
        { pages := lim.min, max := lim.max, byte := fun _ => 0 },
      globals := s.globals ++ (m.globals.zip gvals).map fun (g, v) =>
        { type := g.type, value := v },
      elems := s.elems ++ (m.elems.zip erefs).map fun (e, rs) => { type := e.type, elem := rs },
      datas := s.datas ++ m.datas.map fun d => { data := d.init } }
  (s', inst)

/-- `runelem_i` (§4.5.4). -/
def runElem (i : Nat) (e : Elem) : List Instr :=
  match e.mode with
  | .passive => []
  | .active x off =>
    off ++ [.iconst .w32 0, .iconst .w32 e.init.length, .tableInit x i, .elemDrop i]
  | .declarative => [.elemDrop i]

/-- `rundata_i` (§4.5.4); data segments name memory 0. -/
def runData (i : Nat) (d : Data) : List Instr :=
  match d.mode with
  | .passive => []
  | .active _ off =>
    off ++ [.iconst .w32 0, .iconst .w32 d.init.length, .memoryInit i, .dataDrop i]

/-- The initialization code: element segments, then data segments, then the start call. -/
def initCode (m : Module) : List Instr :=
  (m.elems.zipIdx.flatMap fun (e, i) => runElem i e) ++
  (m.datas.zipIdx.flatMap fun (d, i) => runData i d) ++
  (match m.start with
   | some x => [.call x]
   | none => [])

/-- Successful instantiation of `m` in `s` with `imports` (§4.5.4), giving store `s'` and
instance `inst`. -/
def Instantiated (H : HostSem) (m : Module) (s : Store) (imports : List ExternVal)
    (s' : Store) (inst : ModuleInst) : Prop :=
  ImportsMatch s m imports ∧
  ∃ gvals erefs s₁, allocModule s m imports gvals erefs = (s₁, inst) ∧
    List.Forall₂ (fun g v => Steps H ⟨s₁, ⟨[], inst⟩, g.init.map .plain⟩
      ⟨s₁, ⟨[], inst⟩, [v.instr]⟩) m.globals gvals ∧
    List.Forall₂ (fun e rs => List.Forall₂ (fun ex r => Steps H ⟨s₁, ⟨[], inst⟩, ex.map .plain⟩
      ⟨s₁, ⟨[], inst⟩, [(Val.ref r).instr]⟩) e.init rs) m.elems erefs ∧
    Steps H ⟨s₁, ⟨[], inst⟩, (initCode m).map .plain⟩ ⟨s', ⟨[], inst⟩, []⟩

end FVA.Wasm.Exec

namespace FVA.Wasm.Exec

open FVA.Wasm

/-- Calling export `name` (if the instance exports it) with no arguments runs to completion
with no results, from `s` to `s'`; an absent export leaves the store unchanged. -/
def RunsExport (H : HostSem) (inst : ModuleInst) (name : String) (s s' : Store) : Prop :=
  match inst.exportFunc name with
  | some a => Steps H (invokeConfig s a []) ⟨s', ⟨[], {}⟩, []⟩
  | none => s' = s

/-- A dylink.0 module is ready (tool-conventions DynamicLinking.md): instantiated, then its
exported `__wasm_apply_data_relocs` and `__wasm_call_ctors` have run, in that order, before any
other export is called. The loader's import choices (`env.memory`, `env.__memory_base`,
`env.__table_base`, `env.__stack_pointer`, `GOT.*`) are whatever `imports` supplies; claims
quantify over them under their own preconditions. -/
def LoaderReady (H : HostSem) (m : Module) (s : Store) (imports : List ExternVal) (s' : Store)
    (inst : ModuleInst) : Prop :=
  ∃ s₁ s₂, Instantiated H m s imports s₁ inst ∧
    RunsExport H inst "__wasm_apply_data_relocs" s₁ s₂ ∧
    RunsExport H inst "__wasm_call_ctors" s₂ s'

end FVA.Wasm.Exec
