import FVA.Spec.Valid.Instr

/-!
# Module validity (reviewed spec; contract U6 T2)

Transcribes WebAssembly 2.0 §3.2 (types) and §3.4 (modules) for FVA's profile: the module
context is built from the module's own definitions (imports first), globals and segments are
checked under the context of the imported globals alone, functions under the full one; at most
one memory (imported or defined), distinct export names, and `C.refs` = the function indices the
module names outside function bodies and the start function (§3.4.10). The syntax is Wasm 3.0's
P′ (`docs/contracts/U28a-profile.md`); until P′ validation (U28c) a valid module stays inside the
2.0 profile (`Module.inP2`), and element segments are typed by the nullable projection of 3.0's
`(ref func)` (2.0 types `ref.func` as `funcref`).
-/

namespace FVA.Wasm.Valid

open FVA.Wasm

/-- `⊢ limits : k` (§3.2.1): the minimum, and a maximum at least the minimum, are at most `k`. -/
def _root_.FVA.Wasm.Limits.Ok (l : Limits) (k : Nat) : Prop :=
  l.min ≤ k ∧ ∀ mx, l.max = some mx → l.min ≤ mx ∧ mx ≤ k

/-- `⊢ tabletype ok` (§3.2.4): limits within 2^32 − 1 elements. -/
def _root_.FVA.Wasm.TableType.Ok (t : TableType) : Prop := t.limits.Ok (2 ^ 32 - 1)

/-- `⊢ memtype ok` (§3.2.5): limits within 2^16 pages. -/
def memTypeOk (l : Limits) : Prop := l.Ok (2 ^ 16)

/-- `C ⊢ importdesc : externtype` (§3.4.9): the type exists (functions) or is valid; no tags in
the 2.0 profile. -/
def _root_.FVA.Wasm.ImportDesc.Ok (C : Context) : ImportDesc → Prop
  | .func x => x < C.types.length
  | .table tt => tt.Ok
  | .mem lim => memTypeOk lim
  | .global _ => True
  | .tag _ => False

/-- The imported function types (`funcs(it*)`). -/
def importFuncs (C : Context) (ims : List Import) : List FuncType :=
  ims.filterMap fun im => match im.desc with
    | .func x => C.types[x]?
    | _ => none

/-- The imported table types (`tables(it*)`). -/
def importTables (ims : List Import) : List TableType :=
  ims.filterMap fun im => match im.desc with
    | .table tt => some tt
    | _ => none

/-- The imported memory types (`mems(it*)`). -/
def importMems (ims : List Import) : List Limits :=
  ims.filterMap fun im => match im.desc with
    | .mem lim => some lim
    | _ => none

/-- The imported global types (`globals(it*)`). -/
def importGlobals (ims : List Import) : List GlobalType :=
  ims.filterMap fun im => match im.desc with
    | .global gt => some gt
    | _ => none

/-- The function indices `ref.func` names in an expression. -/
def Expr.refFuncs (e : Expr) : List Nat :=
  e.filterMap fun | .refFunc x => some x | _ => none

/-- `C.refs` (§3.4.10): the function indices occurring in the module outside its functions and
start function — in global initializers, element segments (initializers and offsets) and
exports. -/
def declaredRefs (m : Module) : List Nat :=
  m.globals.flatMap (fun g => Expr.refFuncs g.init) ++
  m.elems.flatMap (fun e => e.init.flatMap Expr.refFuncs ++ match e.mode with
    | .active _ off => Expr.refFuncs off
    | _ => []) ++
  m.exports.filterMap fun ex => match ex.desc with
    | .func x => some x
    | _ => none

/-- The module context `C` of §3.4.10: types, imports followed by definitions, element reference
types, the data count, the declared references; no locals, labels or return type. -/
def moduleContext (m : Module) : Context :=
  let C₀ : Context := { types := m.typeList }
  { types := m.typeList,
    funcs := importFuncs C₀ m.imports ++ m.funcs.filterMap fun f => m.typeList[f.type]?,
    tables := importTables m.imports ++ m.tables.map (·.type),
    mems := importMems m.imports ++ m.mems,
    globals := importGlobals m.imports ++ m.globals.map (·.type),
    elems := m.elems.map (·.type.nullable),
    datas := m.datas.length,
    refs := declaredRefs m }

/-- A value type with a default value (numbers, nullable references): every local of the 2.0
profile, until U28c tracks the initialization of the others. -/
def _root_.FVA.Wasm.ValType.defaultable : ValType → Bool
  | .num _ => true
  | .ref t => t.null

/-- `C ⊢ func : ft` (§3.4.1): the type exists; the declared locals have defaults; the body has
the result type under the parameters and declared locals, with the results as the one label and
the return type. -/
def FuncT (C : Context) (f : Func) (ft : FuncType) : Prop :=
  C.types[f.type]? = some ft ∧ (∀ l ∈ f.locals, l.2.defaultable = true) ∧
    ExprT { C with locals := ft.params.map (1, ·) ++ f.locals, labels := [ft.results],
                   return_ := some ft.results } f.body ft.results

/-- `C ⊢ elemmode : t` (§3.4.5). -/
def _root_.FVA.Wasm.ElemMode.Ok (C : Context) (t : RefType) : ElemMode → Prop
  | .passive | .declarative => True
  | .active x off => (∃ tt, C.tables[x]? = some tt ∧ tt.elem = t) ∧
      ExprT C off [.num .i32] ∧ ConstExpr C off

/-- `C ⊢ datamode ok` (§3.4.6). -/
def _root_.FVA.Wasm.DataMode.Ok (C : Context) : DataMode → Prop
  | .passive => True
  | .active x off => (∃ lim, C.mems[x]? = some lim) ∧ ExprT C off [.num .i32] ∧ ConstExpr C off

/-- `C ⊢ exportdesc : externtype` (§3.4.8): the exported entity exists; no tags in the 2.0
profile. -/
def _root_.FVA.Wasm.ExportDesc.Ok (C : Context) : ExportDesc → Prop
  | .func x => x < C.funcs.length
  | .table x => x < C.tables.length
  | .mem x => x < C.mems.length
  | .global x => x < C.globals.length
  | .tag _ => False

/-- Heap types of the 2.0 profile: function and external references. -/
def _root_.FVA.Wasm.HeapType.inP2 : HeapType → Bool
  | .abs .func | .abs .extern => true
  | _ => false

/-- Value types of the 2.0 profile: numbers, nullable function or external references. -/
def _root_.FVA.Wasm.ValType.inP2 : ValType → Bool
  | .num _ => true
  | .ref t => t.null && t.heap.inP2

/-- Block types of the 2.0 profile. -/
def _root_.FVA.Wasm.BlockType.inP2 : BlockType → Bool
  | .val t => t.inP2
  | _ => true

mutual
/-- An instruction of the 2.0 profile: none of P′'s additions, and every type it names (nested
bodies included) a 2.0 type. -/
def _root_.FVA.Wasm.Instr.inP2 : Instr → Bool
  | .refNull ht => ht.inP2
  | .select (some ts) => ts.all ValType.inP2
  | .block bt body | .loop bt body => bt.inP2 && instrsInP2 body
  | .if_ bt thn els => bt.inP2 && instrsInP2 thn && instrsInP2 els
  | .throw _ | .throwRef | .tryTable .. | .returnCall _ | .returnCallIndirect .. | .callRef _
  | .returnCallRef _ | .refAsNonNull | .brOnNull _ | .brOnNonNull _ => false
  | _ => true
/-- Every instruction of the sequence is of the 2.0 profile. -/
def instrsInP2 : List Instr → Bool
  | [] => true
  | i :: is => i.inP2 && instrsInP2 is
end

/-- The module stays inside the 2.0 profile (until U28c): one-member type groups of 2.0 function
types, no tags, tag imports or tag exports, 2.0 types at every annotation, tables of nullable
function or external references starting as null, element segments of function or external
references (non-null ones initialized by `ref.func`), 2.0 instructions only. -/
def _root_.FVA.Wasm.Module.inP2 (m : Module) : Bool :=
  let ft (f : FuncType) := f.params.all ValType.inP2 && f.results.all ValType.inP2
  let offset : Option Expr → Bool | some e => instrsInP2 e | none => true
  m.types.all (fun g => match g with | [f] => ft f | _ => false) && m.tags.isEmpty &&
  m.imports.all (fun im => match im.desc with
    | .table tt => ValType.inP2 (.ref tt.elem) | .global gt => gt.val.inP2 | .tag _ => false
    | _ => true) &&
  m.tables.all (fun t => ValType.inP2 (.ref t.type.elem) &&
    match t.init, t.type.elem.heap with
    | [.refNull (.abs a)], .abs b => a == b
    | _, _ => false) &&
  m.funcs.all (fun f => f.locals.all (fun l => l.2.inP2) && instrsInP2 f.body) &&
  m.globals.all (fun g => g.type.val.inP2 && instrsInP2 g.init) &&
  m.elems.all (fun e => e.type.heap.inP2 &&
    e.init.all instrsInP2 &&
    -- a non-null segment: `ref.func` initializers alone (3.0 types each at the declared type)
    (e.type.null || e.init.all fun ex => match ex with | [.refFunc _] => true | _ => false) &&
    offset (match e.mode with | .active _ off => some off | _ => none)) &&
  m.datas.all (fun d => offset (match d.mode with | .active _ off => some off | _ => none)) &&
  m.exports.all (fun ex => match ex.desc with | .tag _ => false | _ => true)

/-- `⊢ module : it* → et*` (§3.4.10). -/
structure ModuleValid (m : Module) : Prop where
  /-- Inside the 2.0 profile (until U28c). -/
  profile : m.inP2 = true
  /-- Every function index names an existing type, and the context lists one type per
  function (`ft*` in index order). -/
  funcTypes : ∀ f ∈ m.funcs, f.type < m.typeList.length
  /-- Imports are valid (§3.4.9). -/
  imports : ∀ im ∈ m.imports, im.desc.Ok (moduleContext m)
  /-- Functions are valid under `C`. -/
  funcs : ∀ f ∈ m.funcs, ∃ ft, FuncT (moduleContext m) f ft
  /-- Tables and memories are valid. -/
  tables : ∀ t ∈ m.tables, t.type.Ok
  mems : ∀ lim ∈ m.mems, memTypeOk lim
  /-- Globals: a constant initializer of the global's type, under `C'` (imported globals
  alone). -/
  globals : ∀ g ∈ m.globals,
    ExprT { moduleContext m with globals := importGlobals m.imports } g.init [g.type.val] ∧
      ConstExpr { moduleContext m with globals := importGlobals m.imports } g.init
  /-- Element segments: constant initializers of the segment's type and a valid mode,
  under `C'`. -/
  elems : ∀ e ∈ m.elems,
    (∀ ex ∈ e.init,
      ExprT { moduleContext m with globals := importGlobals m.imports } ex [.ref e.type.nullable] ∧
        ConstExpr { moduleContext m with globals := importGlobals m.imports } ex) ∧
      e.mode.Ok { moduleContext m with globals := importGlobals m.imports } e.type.nullable
  /-- Data segments: a valid mode under `C'`. -/
  datas : ∀ d ∈ m.datas, d.mode.Ok { moduleContext m with globals := importGlobals m.imports }
  /-- Segment payloads are vectors, which have fewer than `2^32` elements (§2.2.5; the AST's
  lists do not carry the bound): instantiation materializes both lengths as `i32` constants. -/
  elemLengths : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  dataLengths : ∀ d ∈ m.datas, d.init.length < 2 ^ 32
  /-- The start function exists and has type `[] → []`. -/
  start : ∀ x, m.start = some x → (moduleContext m).funcs[x]? = some ⟨[], []⟩
  /-- Exports name existing entities, under distinct names. -/
  exports : ∀ ex ∈ m.exports, ex.desc.Ok (moduleContext m)
  exportNames : (m.exports.map (·.name)).Nodup
  /-- At most one memory, imported or defined. -/
  oneMemory : (moduleContext m).mems.length ≤ 1

end FVA.Wasm.Valid
