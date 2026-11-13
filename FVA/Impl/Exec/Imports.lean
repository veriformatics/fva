import FVA.Spec.Exec.Instantiate
import FVA.Impl.TypeEq

/-!
# Import matching (verified implementation)

A decidable reading of `ImportsMatch` (§4.5.2 external type matching): the official-script runner
checks every module's imports with it, and an `assert_unlinkable` passes only when it fails.
`FVA.Proof.Exec.Imports` proves `importsMatch_iff`.
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

/-- `Limits.Matches` decided. -/
def limitsMatch (l₁ l₂ : Limits) : Bool :=
  Nat.ble l₂.min l₁.min && match l₂.max, l₁.max with
    | none, _ => true
    | some m₂, some m₁ => Nat.ble m₁ m₂
    | some _, none => false

/-- A defined type's heap type below `func`. -/
def defBelowFunc : HeapType → HeapType → Bool
  | .def_ _, .abs .func => true
  | _, _ => false

/-- `ValType.Sub` decided. -/
def valSub : ValType → ValType → Bool
  | .num a, .num b => a == b
  | .ref t₁, .ref t₂ =>
    (!t₁.null || t₂.null) && (decide (t₁.heap = t₂.heap) || defBelowFunc t₁.heap t₂.heap)
  | _, _ => false

/-- `GlobalType.Sub` decided. -/
def globalSub (g₁ g₂ : GlobalType) : Bool :=
  decide (g₁.mutability = g₂.mutability) && match g₂.mutability with
    | .var => decide (g₁.val = g₂.val)
    | .const => valSub g₁.val g₂.val

/-- `ExternVal.Matches` decided, under the importing module's defined types `dts`. -/
def externMatch (s : Store) (dts : List DefType) : ExternVal → ImportDesc → Bool
  | .func a, .func x => match s.funcs[a]?, dts[x]? with
    | some fi, some dt => decide (dt = fi.type)
    | _, _ => false
  | .table a, .table tt => match s.tables[a]? with
    | some t => limitsMatch ⟨t.elem.length, t.type.limits.max⟩ tt.limits &&
        decide (t.type.elem = ⟨tt.elem.null, closeHeap dts tt.elem.heap⟩)
    | none => false
  | .mem a, .mem lim => match s.mems[a]? with
    | some mi => limitsMatch ⟨mi.pages, mi.max⟩ lim
    | none => false
  | .global a, .global gt => match s.globals[a]? with
    | some g => globalSub g.type ⟨gt.mutability, gt.val.mapHeap (closeHeap dts)⟩
    | none => false
  | .tag a, .tag x => match s.tags[a]?, dts[x]? with
    | some ti, some dt => decide (dt = ti.type)
    | _, _ => false
  | _, _ => false

/-- Every import supplied by a matching external value, in order. -/
def importsMatchList (s : Store) (dts : List DefType) : List ExternVal → List Import → Bool
  | [], [] => true
  | ev :: evs, im :: ims => externMatch s dts ev im.desc && importsMatchList s dts evs ims
  | _, _ => false

/-- `ImportsMatch` decided. -/
def importsMatch (s : Store) (m : Module) (imports : List ExternVal) : Bool :=
  importsMatchList s m.defTypes imports m.imports

end FVA.Wasm.Exec.Ref
