import FVATest.Subjects.CppEH.Lifted
import FVA.Impl.Exec.Machine
import FVA.Impl.Exec.Imports

/-! D29/U28f I4: `eh` on the verified machine. `Lifted.bytes` decoded (`decode_eq` = this module
is `Lifted.module`), import i bound to host function i (the module's defined type), instantiated
once; each input then runs `eh` from the instantiated store (a fresh process per call, as
`wasmtime run --invoke`) through `Machine.sysRun` with a fail-closed WASI stub. The `#eval` at the
end fails the build on any input off the source contract. U29b's executable host replaces the
stub. Test-only: no proof module in the import closure, so a planted machine bug reaches the run.
-/

namespace Subjects.CppEH.Run

open FVA.Wasm FVA.Wasm.Exec

/-- The artifact, decoded. -/
def mod : Module :=
  match Decode.decode Lifted.bytes Lifted.len with
  | .ok m => m
  | .error _ => {}

/-- One host function per import: host id = import index, type = the module's defined type. -/
def hostStore (m : Module) : Machine.MStore × List ExternVal :=
  let fs := m.imports.zipIdx.filterMap fun (im, i) => match im.desc with
    | .func x => m.defTypes[x]?.map fun dt => FuncInst.host dt i
    | _ => none
  (Machine.MStore.ofStore { funcs := fs }, (List.range fs.length).map .func)

/-- WASI stub over memory `mem`, the world counting host calls: `environ_sizes_get(count,
size)` stores u32 0 at both pointers and returns errno 0 (wasmtime's default empty
environment); a pointer past the memory or any other import has no outcome (the run stops). -/
def stub (m : Module) (mem : Nat) (σ id : Nat) (ms : Machine.MStore) (args : List Val) :
    Option (Nat × Machine.MStore × Machine.MHostOut) :=
  match m.imports[id]?, args, ms.mems[mem]? with
  | some im, [.i32 p, .i32 q], some mm =>
    if im.module == "wasi_snapshot_preview1" && im.name == "environ_sizes_get" &&
        p.toNat + 4 ≤ mm.size && q.toNat + 4 ≤ mm.size then
      let mm' := (mm.write p.toNat 4 0).write q.toNat 4 0
      some (σ + 1, { ms with mems := ms.mems.set mem mm' }, .returned [.i32 0])
    else none
  | _, _, _ => none

/-- The source contract (`eh.cpp`): an even input's successor, an odd input XOR `0xa5a5a5a5`. -/
def expected (x : Nat) : Nat :=
  if x % 2 = 0 then (x + 1) % 2 ^ 32 else x ^^^ 0xa5a5a5a5

/-- The acceptance oracle's 8 bit patterns + 64 from a fixed-seed LCG (Numerical Recipes). -/
def inputs : List Nat :=
  [0, 1, 2, 3, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 2, 2 ^ 32 - 1] ++
    ((List.range 64).foldl (fun (s, xs) _ =>
      let s' := (1664525 * s + 1013904223) % 2 ^ 32
      (s', xs ++ [s'])) (0x2545f491, [])).2

/-- Instruction fuel per call; the odd path needs far less. -/
def fuel : Nat := 10000000

/-- Every input off the contract, described: ending, fuel, host calls, exception instances. -/
def failures : Except String (List String) := do
  let (s₀, imps) := hostStore mod
  unless Ref.importsMatch s₀.abs mod imps do throw "the host functions do not match the imports"
  let some (s₁, inst) := Machine.instantiate fuel s₀ mod imps | throw "instantiation failed"
  let exported name := (inst.exports.find? (·.name == name)).map (·.value)
  let some (ExternVal.func f) := exported "eh" | throw "no export eh"
  let some (ExternVal.mem mem) := exported "memory" | throw "no exported memory"
  return inputs.filterMap fun x =>
    let (calls, m, exhausted) := Machine.sysRun (fun _ => none) (stub mod mem) fuel
      (0, Machine.MState.ofInvoke s₁ f [.i32 (BitVec.ofNat 32 x)])
    let exns := m.store.base.exns.length
    let want := if x % 2 = 0 then 0 else 1
    match m.ending with
    | .returned [.i32 r] =>
      if !exhausted && r.toNat == expected x && calls == want && exns == want then none
      else some s!"x={x}: returned {r.toNat} (want {expected x}), exhausted {exhausted}, \
        {calls} host calls + {exns} exceptions (want {want} + {want})"
    | .returned _ => some s!"x={x}: returned values of another shape"
    | .trapped => some s!"x={x}: trapped after {calls} host calls"
    | .thrown a => some s!"x={x}: uncaught exception {a}"
    | .stuck => some s!"x={x}: stopped (exhausted {exhausted}) after {calls} host calls"

#eval show IO Unit from do
  match failures with
  | .error e => throw <| IO.userError s!"CppEH run: {e}"
  | .ok [] => pure ()
  | .ok bad => throw (IO.userError
      s!"CppEH run: {bad.length} of {inputs.length} inputs off the contract: {bad}")

end Subjects.CppEH.Run
