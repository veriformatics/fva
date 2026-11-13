import FVA.Impl.Exec.Imports

/-!
# Import matching decides `ImportsMatch`
-/

namespace FVA.Wasm.Exec.Ref

open FVA.Wasm FVA.Wasm.Exec

theorem limitsMatch_iff (l₁ l₂ : Limits) : limitsMatch l₁ l₂ = true ↔ Limits.Matches l₁ l₂ := by
  rcases l₁ with ⟨min₁, max₁⟩
  rcases l₂ with ⟨min₂, max₂⟩
  cases max₂ <;> cases max₁ <;> simp [limitsMatch, Limits.Matches]

theorem externMatch_iff (s : Store) (types : List FuncType) (ev : ExternVal) (d : ImportDesc) :
    externMatch s types ev d = true ↔ ev.Matches s types d := by
  cases ev with
  | func a => cases d with
    | func x =>
      simp only [externMatch, ExternVal.Matches]
      cases h₁ : s.funcs[a]? <;> cases h₂ : types[x]? <;> simp [eq_comm]
    | _ => simp [externMatch, ExternVal.Matches]
  | table a => cases d with
    | table tt =>
      simp only [externMatch, ExternVal.Matches]
      cases h : s.tables[a]? <;> simp [limitsMatch_iff]
    | _ => simp [externMatch, ExternVal.Matches]
  | mem a => cases d with
    | mem lim =>
      simp only [externMatch, ExternVal.Matches]
      cases h : s.mems[a]? <;> simp [limitsMatch_iff]
    | _ => simp [externMatch, ExternVal.Matches]
  | global a => cases d with
    | global gt =>
      simp only [externMatch, ExternVal.Matches]
      cases h : s.globals[a]? <;> simp
    | _ => simp [externMatch, ExternVal.Matches]

theorem importsMatchList_iff (s : Store) (types : List FuncType) :
    ∀ (evs : List ExternVal) (ims : List Import), importsMatchList s types evs ims = true ↔
      List.Forall₂ (fun ev im => ev.Matches s types im.desc) evs ims
  | [], [] => by simp [importsMatchList]
  | ev :: evs, im :: ims => by
    simp [importsMatchList, externMatch_iff, importsMatchList_iff s types evs ims]
  | [], _ :: _ => by simp [importsMatchList]
  | _ :: _, [] => by simp [importsMatchList]

theorem importsMatch_iff (s : Store) (m : Module) (imports : List ExternVal) :
    importsMatch s m imports = true ↔ ImportsMatch s m imports :=
  importsMatchList_iff s m.typeList imports m.imports

end FVA.Wasm.Exec.Ref
