import FVA.Spec.Valid.Instr

/-!
# Module validity (reviewed spec; contracts U6 T2, U28c V5)

Transcribes WebAssembly 3.0 SpecTec `859d3232` `2.1` (type validity) and `2.4` (modules) for
profile P′: recursive type groups valid in order (each member names earlier types or members of
its own group), then the module context built from the module's own definitions (imports first),
every type closed under the module's defined types (`docs/contracts/U28a-profile.md` A2). Tags,
globals and tables are checked under `C′` (the imported globals; each global initializer also
sees the earlier defined globals, a table initializer the imported ones alone), functions and
element and data segments under the full context `C`; at most one memory (P′ has no
multi-memory), distinct export names, and `C.refs` = the function indices the module names in
globals, tables, element segments and exports (`$funcidx_nonfuncs`).
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

/-- `⊢ limits : k` (`Limits_ok`): the minimum, and a maximum at least the minimum, are at most
`k`. -/
def _root_.FVA.Wasm.Limits.Ok (l : Limits) (k : Nat) : Prop :=
  l.min ≤ k ∧ ∀ mx, l.max = some mx → l.min ≤ mx ∧ mx ≤ k

/-- `⊢ tabletype ok` (`Tabletype_ok`, limits part): within 2^32 − 1 elements. -/
def _root_.FVA.Wasm.TableType.Ok (t : TableType) : Prop := t.limits.Ok (2 ^ 32 - 1)

/-- `⊢ memtype ok` (`Memtype_ok`): limits within 2^16 pages. -/
def memTypeOk (l : Limits) : Prop := l.Ok (2 ^ 16)

/-- `C ⊢ externtype : OK` (`Externtype_ok`) of a source import description: a function or tag by
a defined type that expands to a function type (a tag's without results), a table type with
valid limits and element type, a memory type, a global type with a valid value type. -/
def _root_.FVA.Wasm.ImportDesc.Ok (C : Context) : ImportDesc → Prop
  | .func x => ∃ ft, C.typeAt x = some ft
  | .table tt => tt.Ok ∧ tt.elem.heap.Src C.types.length
  | .mem lim => memTypeOk lim
  | .global gt => gt.val.Src C.types.length
  | .tag x => ∃ ts, C.typeAt x = some ⟨ts, []⟩

/-- The imported functions' defined types (`funcs(xt_I*)`). -/
def importFuncs (dts : List DefType) (ims : List Import) : List DefType :=
  ims.filterMap fun im => match im.desc with
    | .func x => dts[x]?
    | _ => none

/-- The imported tags' defined types (`tags(xt_I*)`). -/
def importTags (dts : List DefType) (ims : List Import) : List DefType :=
  ims.filterMap fun im => match im.desc with
    | .tag x => dts[x]?
    | _ => none

/-- The imported table types, closed (`tables(xt_I*)`). -/
def importTables (dts : List DefType) (ims : List Import) : List TableType :=
  ims.filterMap fun im => match im.desc with
    | .table tt => some (tt.close dts)
    | _ => none

/-- The imported memory types (`mems(xt_I*)`). -/
def importMems (ims : List Import) : List Limits :=
  ims.filterMap fun im => match im.desc with
    | .mem lim => some lim
    | _ => none

/-- The imported global types, closed (`globals(xt_I*)`). -/
def importGlobals (dts : List DefType) (ims : List Import) : List GlobalType :=
  ims.filterMap fun im => match im.desc with
    | .global gt => some (gt.close dts)
    | _ => none

/-- The function indices `ref.func` names in an expression. -/
def Expr.refFuncs (e : Expr) : List Nat :=
  e.filterMap fun | .refFunc x => some x | _ => none

/-- `C.refs` (`$funcidx_nonfuncs`): the function indices occurring in the module's globals,
tables, element segments (initializers and offsets) and exports. -/
def declaredRefs (m : Module) : List Nat :=
  m.globals.flatMap (fun g => Expr.refFuncs g.init) ++
  m.tables.flatMap (fun t => Expr.refFuncs t.init) ++
  m.elems.flatMap (fun e => e.init.flatMap Expr.refFuncs ++ match e.mode with
    | .active _ off => Expr.refFuncs off
    | _ => []) ++
  m.exports.filterMap fun ex => match ex.desc with
    | .func x => some x
    | _ => none

/-- The module context `C` of `Module_ok`: the defined types, imports followed by definitions
(types closed), the element types, the data count, the declared references; no locals, labels or
return type. -/
def moduleContext (m : Module) : Context :=
  let dts := m.defTypes
  { types := dts,
    funcs := importFuncs dts m.imports ++ m.funcs.filterMap fun f => dts[f.type]?,
    tags := importTags dts m.imports ++ m.tags.filterMap fun t => dts[t.type]?,
    tables := importTables dts m.imports ++ m.tables.map (·.type.close dts),
    mems := importMems m.imports ++ m.mems,
    globals := importGlobals dts m.imports ++ m.globals.map (·.type.close dts),
    elems := m.elems.map (·.type.close dts),
    datas := m.datas.length,
    refs := declaredRefs m }

/-- The context of the `k`-th defined global's initializer (`Globals_ok` under `C′`): the
imported globals and the `k` defined before it. A table initializer's context = `k = 0`. -/
def globalContext (m : Module) (k : Nat) : Context :=
  { moduleContext m with
    globals := importGlobals m.defTypes m.imports ++
      (m.globals.take k).map (·.type.close m.defTypes) }

/-- A value type with a default value (numbers, nullable references; `Defaultable`). -/
def _root_.FVA.Wasm.ValType.defaultable : ValType → Bool
  | .num _ => true
  | .ref t => t.null

/-- `C ⊢ func : dt` (`Func_ok`, `Local_ok`): the function's defined type expands to `t₁* → t₂*`;
the declared locals are valid, set exactly when defaultable; the body has the results under the
parameters (set) and the locals, with the results as the one label and the return type. -/
def FuncT (C : Context) (f : Func) (dt : DefType) : Prop :=
  C.types[f.type]? = some dt ∧ ∃ ft, dt.expand = some ft ∧
    (∀ l ∈ f.locals, l.2.Src C.types.length) ∧
    ExprT { C with
      locals := ft.params.map (1, ⟨true, ·⟩) ++
        f.locals.map fun l => (l.1, ⟨l.2.defaultable, C.close l.2⟩),
      labels := [ft.results], return_ := some ft.results } f.body ft.results

/-- `C ⊢ elemmode : rt` (`Elemmode_ok`): an active segment's table holds a supertype of the
segment's elements; its offset is a constant `i32` expression. -/
def _root_.FVA.Wasm.ElemMode.Ok (C : Context) (rt : RefType) : ElemMode → Prop
  | .passive | .declarative => True
  | .active x off => (∃ tt, C.tables[x]? = some tt ∧ ValType.Sub (.ref rt) (.ref tt.elem)) ∧
      ExprT C off [.num .i32] ∧ ConstExpr C off

/-- `C ⊢ datamode ok` (`Datamode_ok`). -/
def _root_.FVA.Wasm.DataMode.Ok (C : Context) : DataMode → Prop
  | .passive => True
  | .active x off => (∃ lim, C.mems[x]? = some lim) ∧ ExprT C off [.num .i32] ∧ ConstExpr C off

/-- `C ⊢ externidx : externtype` (`Externidx_ok`): the exported entity exists. -/
def _root_.FVA.Wasm.ExportDesc.Ok (C : Context) : ExportDesc → Prop
  | .func x => x < C.funcs.length
  | .table x => x < C.tables.length
  | .mem x => x < C.mems.length
  | .global x => x < C.globals.length
  | .tag x => x < C.tags.length

/-- `⊢ module : it* → et*` (`Module_ok`). -/
structure ModuleValid (m : Module) : Prop where
  /-- The type groups are valid in order (`Types_ok`). -/
  types : TypesSeq m.types 0
  /-- Imports are valid (`Import_ok`, under the defined types). -/
  imports : ∀ im ∈ m.imports, im.desc.Ok (moduleContext m)
  /-- Tags name function types without results (`Tag_ok`). -/
  tags : ∀ t ∈ m.tags, ∃ ts, (moduleContext m).typeAt t.type = some ⟨ts, []⟩
  /-- Globals: a valid type and a constant initializer of it, under the imported and the earlier
  globals (`Globals_ok`). -/
  globals : ∀ k (g : Global), m.globals[k]? = some g → g.type.val.Src m.defTypes.length ∧
    ExprT (globalContext m k) g.init [(g.type.close m.defTypes).val] ∧
      ConstExpr (globalContext m k) g.init
  /-- Memories are valid (`Mem_ok`). -/
  mems : ∀ lim ∈ m.mems, memTypeOk lim
  /-- Tables: a valid type and a constant initializer of its element type, under the imported
  globals (`Table_ok`). -/
  tables : ∀ t ∈ m.tables, t.type.Ok ∧ t.type.elem.heap.Src m.defTypes.length ∧
    ExprT (globalContext m 0) t.init [.ref (t.type.elem.close m.defTypes)] ∧
      ConstExpr (globalContext m 0) t.init
  /-- Functions are valid under `C` (`Func_ok`); each names an existing type. -/
  funcs : ∀ f ∈ m.funcs, ∃ dt, FuncT (moduleContext m) f dt
  /-- Element segments: a valid type, constant initializers of it and a valid mode
  (`Elem_ok`). -/
  elems : ∀ e ∈ m.elems, e.type.heap.Src m.defTypes.length ∧
    (∀ ex ∈ e.init, ExprT (moduleContext m) ex [.ref (e.type.close m.defTypes)] ∧
      ConstExpr (moduleContext m) ex) ∧
    e.mode.Ok (moduleContext m) (e.type.close m.defTypes)
  /-- Data segments: a valid mode (`Data_ok`). -/
  datas : ∀ d ∈ m.datas, d.mode.Ok (moduleContext m)
  /-- Segment payloads are vectors, which have fewer than `2^32` elements (the AST's lists do
  not carry the bound): instantiation materializes both lengths as `i32` constants. -/
  elemLengths : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  dataLengths : ∀ d ∈ m.datas, d.init.length < 2 ^ 32
  /-- The start function exists and has type `[] → []` (`Start_ok`). -/
  start : ∀ x, m.start = some x → (moduleContext m).funcType x = some ⟨[], []⟩
  /-- Exports name existing entities (`Export_ok`), under distinct names. -/
  exports : ∀ ex ∈ m.exports, ex.desc.Ok (moduleContext m)
  exportNames : (m.exports.map (·.name)).Nodup
  /-- At most one memory, imported or defined (P′ has no multi-memory). -/
  oneMemory : (moduleContext m).mems.length ≤ 1

end FVA.Wasm.Valid
