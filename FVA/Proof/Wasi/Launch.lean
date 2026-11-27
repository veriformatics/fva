import FVA.Spec.Wasi.World
import FVA.Proof.Valid.Validator
import FVA.Proof.Exec.Instantiate
import FVA.Proof.Exec.Imports

/-!
# `Launch` is satisfiable; a mis-typed WASI import launches nothing (U29a T6)

A minimal WASI command — imports `fd_write` + `proc_exit`, exports its memory and `_start`
(`proc_exit 0`) — launches; the same module importing `fd_write` at type `[] → []` does not
(wasmtime refuses to link it: consultant-13's probe `wrong-signature.wat`).
-/

namespace FVA.Wasi.LaunchExample

open FVA.Wasm FVA.Wasm.Exec FVA.Wasi

/-- `i32`. -/
def i32 : ValType := .num .i32

/-- The command, `fd_write` imported at type `fdWriteTy`. -/
def cmdWith (fdWriteTy : Nat) : Module :=
  { types := [[⟨[i32, i32, i32, i32], [i32]⟩], [⟨[i32], []⟩], [⟨[], []⟩]]
    imports := [⟨"wasi_snapshot_preview1", "fd_write", .func fdWriteTy⟩,
      ⟨"wasi_snapshot_preview1", "proc_exit", .func 1⟩]
    funcs := [⟨2, [], [.iconst .w32 0, .call 1]⟩]
    mems := [⟨1, none⟩]
    exports := [⟨"memory", .mem 0⟩, ⟨"_start", .func 2⟩] }

/-- The well-typed command. -/
def cmd : Module := cmdWith 0

theorem cmd_valid : Valid.ModuleValid cmd := Valid.validate_sound (by decide)

theorem cmd_bind : bind cmd 0 = some .fdWrite ∧ bind cmd 1 = some .procExit := by decide

theorem cmd_instantiates :
    (Ref.instantiate 1000 (hostStore cmd) cmd (hostImports cmd)).isSome := by decide

/-- T6: the command launches at `_start`. -/
theorem cmd_launch : ∃ c mem, Launch cmd "_start" [] c mem := by
  let p := (Ref.instantiate 1000 (hostStore cmd) cmd (hostImports cmd)).get cmd_instantiates
  have hp : Ref.instantiate 1000 (hostStore cmd) cmd (hostImports cmd) = some p := by simp [p]
  have hm : ImportsMatch (hostStore cmd) cmd (hostImports cmd) :=
    (Ref.importsMatch_iff _ _ _).mp (by decide)
  have hI := Ref.instantiate_sound (H := NoHost) hm hp
  have ha : p.2.exportFunc "_start" = some 2 := by decide
  have hmem : p.2.exportMem "memory" = some 0 := by decide
  refine ⟨invokeConfig p.1 2 [], 0, cmd_valid, rfl, by decide, ?_, ?_, p.1, p.2, 2, hI, hmem, ha,
    ?_, rfl⟩
  · intro im h
    simp only [cmd, cmdWith, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro id im h _ _
    match id, h with
    | 0, _ => exact (by decide : (bind cmd 0).isSome = true)
    | 1, _ => exact (by decide : (bind cmd 1).isSome = true)
    | n + 2, h => simp [cmd, cmdWith] at h
  · -- `FuncInst` has no decidable equality: decide a match on it instead
    have hchk : (match p.1.funcs[2]? with
        | some fi => (match fi.type.expand with | some ⟨[], []⟩ => true | _ => false)
        | none => false) = true := by decide
    split at hchk
    · rename_i fi hfi
      refine ⟨fi, ⟨[], []⟩, hfi, ?_, List.Forall₂.nil⟩
      split at hchk
      · assumption
      · simp at hchk
    · simp at hchk

/-- T6: `fd_write` imported at another signature launches nothing. -/
theorem mistyped_no_launch : ¬ ∃ c mem, Launch (cmdWith 2) "_start" [] c mem := by
  rintro ⟨c, mem, -, -, -, -, hk, -⟩
  exact absurd (hk 0 _ rfl rfl rfl) (by decide)

/-- `fd_write` imported at its parameters without its result (`[i32, i32, i32, i32] → []`). -/
def noResult : Module :=
  { cmd with
    types := cmd.types ++ [[⟨[i32, i32, i32, i32], []⟩]]
    imports := [⟨"wasi_snapshot_preview1", "fd_write", .func 3⟩] }

/-- Parameters and results both decide: `noResult`'s import binds no call (wasmtime 50.0.0 refuses
that link, "types incompatible": `scripts/test-checks`' dropped-result link plant). -/
theorem noResult_unbound : bind noResult 0 = none := by decide

end FVA.Wasi.LaunchExample
