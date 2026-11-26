import FVA.Spec.Wasi.Call
import FVA.Spec.Exec.System
import FVA.Spec.Exec.Host
import FVA.Spec.Exec.Instantiate
import FVA.Spec.Valid.Module

/-!
# WASI processes: the world, the environment `E`, launching (reviewed spec)

`world m mem` = what the host calls of module `m` may do (W): an import of `wasi_snapshot_preview1`
with a declared call's signature (host id = import index) acts on the WASI state through memory
`mem`, with every choice WITX leaves open; such a call may also block forever, and outside the
profile domain it may have any typed outcome. Every other import may have any typed outcome,
divergence included. `E m mem` = the virtual host claims assume: in-profile calls return, every
choice is `E`'s (`Choice` fields `none`) except `random_get`'s bytes. `Launch` = `m` instantiated
with one host function per import, export `name` invoked: the configuration a claim starts from.
-/

namespace FVA.Wasi

open FVA.Wasm FVA.Wasm.Exec

/-- A value type's number type (`none` for a reference type). -/
def numOf : ValType → Option NumType
  | .num t => some t
  | .ref _ => none

/-- `ft` is call `c`'s signature. -/
def Call.hasSig (c : Call) (ft : FuncType) : Bool :=
  ft.params.map numOf == c.info.2.map (fun w => some (if w then .i64 else .i32)) &&
    ft.results.map numOf == if c = .procExit then [] else [some .i32]

/-- The function type of import `id` of `m`. -/
def importType (m : Module) (id : Nat) : Option FuncType :=
  match m.imports[id]? with
  | some ⟨_, _, .func x⟩ => m.defTypes[x]?.bind DefType.expand
  | _ => none

/-- The declared call import `id` of `m` binds: a `wasi_snapshot_preview1` import naming one, at
its signature. -/
def bind (m : Module) (id : Nat) : Option Call :=
  match m.imports[id]? with
  | some im =>
    if im.module = "wasi_snapshot_preview1" then
      match Call.ofName im.name, importType m id with
      | some c, some ft => if c.hasSig ft then some c else none
      | _, _ => none
    else none
  | none => none

/-- The request of call `c` on arguments `vs` with memory `mem` of `s`. -/
def reqOf (c : Call) (s : Store) (mem : Nat) (vs : List Val) : Req :=
  match s.mems[mem]?, c.args vs with
  | some m, some a => decode c m a
  | _, _ => ⟨c, [], [], [], []⟩

theorem exec_ne_diverged (σ : State) (c : Call) (s : Store) (mem : Nat) (vs : List Val)
    (ch : Choice) : (exec σ c s mem vs ch).2 ≠ .diverged := by
  unfold exec; split
  · split <;> simp
  · simp

/-- The host calls of module `m`, whose WASI calls use memory address `mem`. -/
def world (m : Module) (mem : Nat) : World where
  St := State
  host σ τ id s vs o :=
    match bind m id with
    | some c =>
      (o = .diverged ∧ τ = σ) ∨
      (inProfile σ c s mem vs ∧
        ∃ ch, ChoiceOK σ (reqOf c s mem vs) ch ∧ (τ, o) = exec σ c s mem vs ch) ∨
      (inProfile σ c s mem vs = false ∧ τ.exited = σ.exited ∧ o ≠ .diverged ∧
        o.Allowed s c.sig.results)
    | none =>
      (o = .diverged ∧ τ = σ) ∨
      (o ≠ .diverged ∧ ∀ ft, importType m id = some ft → o.Allowed s ft.results)
  exited := State.exited
  stay {σ τ id s vs} h := by
    split at h
    · rcases h with ⟨-, h⟩ | ⟨-, ch, -, h⟩ | ⟨-, -, h, -⟩
      · exact h
      · exact absurd (congrArg Prod.snd h).symm (exec_ne_diverged _ _ _ _ _ _)
      · exact absurd rfl h
    · rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd rfl h

/-- The environment claims assume: an in-profile bound call returns, with `E`'s choices except
the random bytes; outside the profile domain and for other imports, no restriction (divergence
included, so no total-correctness claim passes such a call). -/
def E (m : Module) (mem : Nat) : State → State → HostSem := fun σ τ id s vs o =>
  match bind m id with
  | some c => inProfile σ c s mem vs → ∃ b, (τ, o) = exec σ c s mem vs { bytes := b }
  | none => True

/-- The memory address an instance exports under `name`. -/
def _root_.FVA.Wasm.Exec.ModuleInst.exportMem (inst : ModuleInst) (name : String) :
    Option Nat :=
  inst.exports.findSome? fun e =>
    match e.value with
    | .mem a => if e.name = name then some a else none
    | _ => none

/-- One host function per import of `m`: import `i` = host id `i`, of the import's closed
defined type. -/
def hostStore (m : Module) : Store :=
  { funcs := m.imports.mapIdx fun i im =>
      .host (match im.desc with
        | .func x => m.defTypes.getD x ⟨[], 0⟩
        | _ => ⟨[], 0⟩) i }

/-- `hostStore m`'s functions, in import order. -/
def hostImports (m : Module) : List ExternVal := (List.range m.imports.length).map .func

/-- `c` = process `m` started at export `name` with arguments `args`, its WASI calls using memory
address `mem`: `m` valid, without start function or `_initialize` (a reactor's initializer),
importing functions alone, each `wasi_snapshot_preview1` import naming a declared call at that
call's signature (wasmtime refuses to link a mismatch); instantiated with `hostStore m`; exporting
its memory as `memory` and `name` as a function `args` fit. -/
def Launch (m : Module) (name : String) (args : List Val) (c : Config) (mem : Nat) : Prop :=
  Valid.ModuleValid m ∧ m.start = none ∧ (∀ ex ∈ m.exports, ex.name ≠ "_initialize") ∧
  (∀ im ∈ m.imports, ∃ x, im.desc = .func x) ∧
  (∀ id im, m.imports[id]? = some im → im.module = "wasi_snapshot_preview1" →
    (Call.ofName im.name).isSome → (bind m id).isSome) ∧
  ∃ s inst a, Instantiated NoHost m (hostStore m) (hostImports m) s inst ∧
    inst.exportMem "memory" = some mem ∧ inst.exportFunc name = some a ∧ InvokeOK s a args ∧
    c = invokeConfig s a args

end FVA.Wasi
