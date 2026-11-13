import FVA.Spec.Exec.Instantiate

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

/-- `ExternVal.Matches` decided. -/
def externMatch (s : Store) (types : List FuncType) : ExternVal → ImportDesc → Bool
  | .func a, .func x => match s.funcs[a]?, types[x]? with
    | some fi, some ft => decide (fi.type = ft)
    | _, _ => false
  | .table a, .table tt => match s.tables[a]? with
    | some t => limitsMatch ⟨t.elem.length, t.type.limits.max⟩ tt.limits &&
        decide (t.type.elem = tt.elem)
    | none => false
  | .mem a, .mem lim => match s.mems[a]? with
    | some mi => limitsMatch ⟨mi.pages, mi.max⟩ lim
    | none => false
  | .global a, .global gt => match s.globals[a]? with
    | some g => decide (g.type = gt)
    | none => false
  | _, _ => false

/-- Every import supplied by a matching external value, in order. -/
def importsMatchList (s : Store) (types : List FuncType) : List ExternVal → List Import → Bool
  | [], [] => true
  | ev :: evs, im :: ims => externMatch s types ev im.desc && importsMatchList s types evs ims
  | _, _ => false

/-- `ImportsMatch` decided. -/
def importsMatch (s : Store) (m : Module) (imports : List ExternVal) : Bool :=
  importsMatchList s m.typeList imports m.imports

end FVA.Wasm.Exec.Ref
