import FVATest.Subjects.EdgerCpm.Spec
import FVA.Impl.Exec.Ref

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def environmentMem : MemInst := ⟨49152, some 65536, fun _ => 0⟩

-- Non-allocator imports return zero values without entering host semantics.
def stub (ft : FuncType) : FuncInst :=
  .wasm ft {} ⟨0, [], ft.results.map fun t =>
    match t with
    | .num .i32 => .iconst .w32 0
    | .num .i64 => .iconst .w64 0
    | .num .f32 => .fconst .w32 0
    | .num .f64 => .fconst .w64 0
    | .ref t => .refNull t⟩

def environment (m : Module) : Store × List ExternVal := Id.run do
  let mut s : Store := {}
  let mut evs : List ExternVal := []
  for im in m.imports do
    match im.desc with
    | .func x =>
      let ft := m.types.getD x ⟨[], []⟩
      let a := s.funcs.length
      let fi := if a = 12 ∨ a = 13 then .host ft a else stub ft
      evs := evs ++ [.func a]
      s := { s with funcs := s.funcs ++ [fi] }
    | .mem _ =>
      evs := evs ++ [.mem s.mems.length]
      s := { s with mems := s.mems ++ [environmentMem] }
    | .table tt =>
      evs := evs ++ [.table s.tables.length]
      s := { s with tables := s.tables ++
        [{ type := tt, elem := List.replicate tt.limits.min (.null tt.elem) }] }
    | .global gt =>
      let v := if im.name == "__stack_pointer" then Val.i32 65536 else gt.val.default
      evs := evs ++ [.global s.globals.length]
      s := { s with globals := s.globals ++ [{ type := gt, value := v }] }
  return (s, evs)

noncomputable def env : Store := (environment Lifted.module).1
noncomputable def imports : List ExternVal := (environment Lifted.module).2

def limitsCheck (l₁ l₂ : Limits) : Bool :=
  l₂.min ≤ l₁.min && match l₂.max with
  | none => true
  | some m₂ => l₁.max.any (· ≤ m₂)

def externCheck (s : Store) (types : List FuncType) : ExternVal → ImportDesc → Bool
  | .func a, .func x => match s.funcs[a]?, types[x]? with
    | some fi, some ft => fi.type == ft
    | _, _ => false
  | .table a, .table tt => match s.tables[a]? with
    | some t => limitsCheck ⟨t.elem.length, t.type.limits.max⟩ tt.limits && t.type.elem == tt.elem
    | none => false
  | .mem a, .mem lim => match s.mems[a]? with
    | some mi => limitsCheck ⟨mi.pages, mi.max⟩ lim
    | none => false
  | .global a, .global gt => match s.globals[a]? with
    | some g => g.type == gt
    | none => false
  | _, _ => false

theorem limitsCheck_sound {a b : Limits} (h : limitsCheck a b = true) :
    Limits.Matches a b := by
  rcases a with ⟨amin, amax⟩
  rcases b with ⟨bmin, bmax⟩
  cases amax <;> cases bmax <;> simp_all [limitsCheck, Limits.Matches]

theorem externCheck_sound {s : Store} {ts : List FuncType} {ev : ExternVal} {im : ImportDesc}
    (h : externCheck s ts ev im = true) : ev.Matches s ts im := by
  cases ev <;> cases im <;> simp only [externCheck, Bool.false_eq_true] at h
  case func.func a x =>
    cases hf : s.funcs[a]? <;> cases ht : ts[x]? <;> simp_all [ExternVal.Matches]
  case table.table a tt =>
    cases ht : s.tables[a]? <;> simp_all only [Bool.false_eq_true]
    rename_i t
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, ht, limitsCheck_sound h.1, h.2⟩
  case mem.mem a lim =>
    cases hm : s.mems[a]? <;> simp_all only [Bool.false_eq_true]
    rename_i m
    exact ⟨m, hm, limitsCheck_sound h⟩
  case global.global a gt =>
    cases hg : s.globals[a]? <;> simp_all [ExternVal.Matches]

def importsCheck (s : Store) (m : Module) (xs : List ExternVal) : Bool :=
  xs.length == m.imports.length &&
    (xs.zip m.imports).all fun (ev, im) => externCheck s m.types ev im.desc

theorem importsCheck_sound {s : Store} {m : Module} {xs : List ExternVal}
    (h : importsCheck s m xs = true) : ImportsMatch s m xs := by
  simp only [importsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  unfold ImportsMatch
  apply List.forall₂_iff_zip.mpr
  refine ⟨h.1, ?_⟩
  intro ev im hi
  exact externCheck_sound (h.2 (ev, im) hi)

theorem env_matches : ImportsMatch env Lifted.module imports :=
  importsCheck_sound (by decide +kernel)

end Subjects.EdgerCpm.Existence
