import FVATest.Subjects.EdgerCpm.Spec
import FVA.Impl.Exec.Ref
import FVA.Proof.Exec.Imports

namespace Subjects.EdgerCpm.Existence

open FVA.Wasm FVA.Wasm.Exec FVA.Wasm.Exec.Ref

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def environmentMem : MemInst := ⟨49152, some 65536, fun _ => 0⟩

-- Non-allocator imports return zero values without entering host semantics.
def stub (dt : DefType) : FuncInst :=
  .wasm dt {} ⟨0, [], (dt.expand.getD ⟨[], []⟩).results.map fun t =>
    match t with
    | .num .i32 => .iconst .w32 0
    | .num .i64 => .iconst .w64 0
    | .num .f32 => .fconst .w32 0
    | .num .f64 => .fconst .w64 0
    | .ref t => .refNull t.heap⟩

def environment (m : Module) : Store × List ExternVal := Id.run do
  let mut s : Store := {}
  let mut evs : List ExternVal := []
  for im in m.imports do
    match im.desc with
    | .func x =>
      let dt := m.defTypes.getD x ⟨[], 0⟩
      let a := s.funcs.length
      let fi := if a = 12 ∨ a = 13 then .host dt a else stub dt
      evs := evs ++ [.func a]
      s := { s with funcs := s.funcs ++ [fi] }
    | .mem _ =>
      evs := evs ++ [.mem s.mems.length]
      s := { s with mems := s.mems ++ [environmentMem] }
    | .table tt =>
      evs := evs ++ [.table s.tables.length]
      s := { s with tables := s.tables ++
        [{ type := tt, elem := List.replicate tt.limits.min .null }] }
    | .global gt =>
      let v := if im.name == "__stack_pointer" then Val.i32 65536 else gt.val.default.getD (.i32 0)
      evs := evs ++ [.global s.globals.length]
      s := { s with globals := s.globals ++ [{ type := gt, value := v }] }
    | .tag _ => pure ()
  return (s, evs)

noncomputable def env : Store := (environment Lifted.module).1
noncomputable def imports : List ExternVal := (environment Lifted.module).2

theorem env_matches : ImportsMatch env Lifted.module imports :=
  (importsMatch_iff _ _ _).mp (by decide +kernel)

end Subjects.EdgerCpm.Existence
