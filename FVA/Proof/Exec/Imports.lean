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

theorem defBelowFunc_iff (h₁ h₂ : HeapType) :
    defBelowFunc h₁ h₂ = true ↔ ∃ d, h₁ = .def_ d ∧ h₂ = .abs .func := by
  cases h₁ <;> cases h₂ <;> simp [defBelowFunc]
  rename_i a; cases a <;> simp

theorem valSub_iff (a b : ValType) : valSub a b = true ↔ a.Sub b := by
  cases a with
  | num x => cases b <;> simp [valSub, ValType.Sub]
  | ref t₁ => cases b with
    | num _ => simp [valSub, ValType.Sub]
    | ref t₂ =>
      rcases t₁ with ⟨n₁, h₁⟩
      rcases t₂ with ⟨n₂, h₂⟩
      cases n₁ <;> cases n₂ <;> simp [valSub, ValType.Sub, defBelowFunc_iff]

theorem globalSub_iff (g₁ g₂ : GlobalType) : globalSub g₁ g₂ = true ↔ g₁.Sub g₂ := by
  rcases g₂ with ⟨mu, v⟩
  cases mu <;> simp [globalSub, GlobalType.Sub, valSub_iff]

theorem externMatch_iff (s : Store) (dts : List DefType) (ev : ExternVal) (d : ImportDesc) :
    externMatch s dts ev d = true ↔ ev.Matches s dts d := by
  cases ev with
  | func a => cases d with
    | func x =>
      simp only [externMatch, ExternVal.Matches]
      cases h₁ : s.funcs[a]? <;> cases h₂ : dts[x]? <;> simp
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
      cases h : s.globals[a]? <;> simp [globalSub_iff]
    | _ => simp [externMatch, ExternVal.Matches]
  | tag a => cases d with
    | tag x =>
      simp only [externMatch, ExternVal.Matches]
      cases h₁ : s.tags[a]? <;> cases h₂ : dts[x]? <;> simp
    | _ => simp [externMatch, ExternVal.Matches]

theorem importsMatchList_iff (s : Store) (dts : List DefType) :
    ∀ (evs : List ExternVal) (ims : List Import), importsMatchList s dts evs ims = true ↔
      List.Forall₂ (fun ev im => ev.Matches s dts im.desc) evs ims
  | [], [] => by simp [importsMatchList]
  | ev :: evs, im :: ims => by
    simp [importsMatchList, externMatch_iff, importsMatchList_iff s dts evs ims]
  | [], _ :: _ => by simp [importsMatchList]
  | _ :: _, [] => by simp [importsMatchList]

theorem importsMatch_iff (s : Store) (m : Module) (imports : List ExternVal) :
    importsMatch s m imports = true ↔ ImportsMatch s m imports :=
  importsMatchList_iff s m.defTypes imports m.imports

end FVA.Wasm.Exec.Ref
