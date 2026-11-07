# U26 contract — optimized machine (D30) (tier: kernel)

Purpose: run long executions fast in compiled code (every official script, `memory_copy` included) and inside the kernel (D28's segment theorems), every machine result a reference-stepper result (Decisions: Self-verification; Language + Wasm reach "Machine"; U4 I1). Consumers: `scripts/test-spec` + `scripts/test-char` (runner), U27 (system layer, host steps, `machineRun_must`), U28d (P'), U29 (WASI, checkpoints).

## Interface (verified implementation, `FVA/Impl/Exec/{Chunks,Machine}.lean`)
- `Chunks` = persistent binary trie over address bits (`z` = all-zero subtree, `leaf c` = `2^W` bytes packed little-endian in one `Nat`, `node l r`; `W = 6`, every proof generic in `W`); `MMem` = `{ pages, max, depth, data }` covering `[0, 2^(depth + W))`; `get`/`set`, `read`/`write`, `readBytes`/`writeBytes`, `fill`, `copy`, `init`, `grow` (root wrapped until the size fits), `alloc`; `MMem.abs m = { pages, max, byte := fun a => UInt8.ofNat (m.byte a) }` (lazy: no materialization).
- `MStore` = `{ base : Store, mems : List MMem }` (`base.mems` never read); `MStore.abs s = { s.base with mems := s.mems.map MMem.abs }`.
- `MState` = `{ store, frame, stack : List Val (top first), code : List AInstr, ctl : List Ctl }`; `Ctl` = `label n cont saved rest` | `frame n caller saved rest` (innermost first); `abs` = `wrap ctl frame (vals stack.reverse ++ code)`, each entry outward wrapping the inner sequence as `vals saved.reverse ++ [.label n cont inner] ++ rest` / `… [.frame n f inner] …`.
- `step : MState → Option MState`: a value moves to `stack`; a plain non-control, non-memory instruction delegates to `Ref.instrStep` on `store.abs`; loads/stores + `memory.size`/`grow` + bulk memory run on the trie; `block`, `loop`, `if`, `br*`, `return`, `call*`, block + function exits on `ctl`; `trap` collapses to `[.trap]` with the outermost frame. `none` = no step; `ending` classifies it (`returned vs` | `trapped` | `stuck`).
- `run : Nat → MState → MState × Bool` (fuel; `true` = fuel ran out); `ofInvoke`; `MStore.alloc` (= `allocModule` + trie memories), `initRun`, `instantiate` mirroring `Ref.instantiate`. `MMem.ofMemInst`/`MStore.ofStore` = runner glue (unproven, fixtures only).

## Theorems (`FVA/Proof/Exec/{Chunks,Machine}.lean`; kernel-checked over the whole domain ⇒ no property tests, `.claude/rules/fva-gate.md` test form)
- Invariant: `MMem.Inv` = `WF ∧ Cover ∧ ZeroTail ∧ pages ≤ 2^16`; `MState.Inv` = every memory's `Inv` (control needs none: `abs` rebuilds it).
- T1 `step_sim`: `m.Inv → m.step = some m' → m'.Inv ∧ ∃ k, stepN k m.abs = some m'.abs`; `run_sim` = the same for `run n`; `stepN_steps`: `stepN k c = some c' → Steps H c c'` for every host semantics `H`.
- T2 `abs_returned`: `m.ending = .returned vs → Final m.abs (.returned m.store.abs vs)`; `abs_trapped`: `m.ending = .trapped → Final m.abs (.trapped m.store.abs)`.
- T4 `abs_ofInvoke`: `(ofInvoke s a args).abs = invokeConfig s.abs a args`; `alloc_abs`/`alloc_inv`: `MStore.alloc` = `allocModule` on the abstraction, invariant kept (memory minimum ≤ 2^16 pages, as validation ensures); `instantiate_sound`: `ImportsMatch s.abs m imports` + `instantiate fuel s m imports = some (s', inst)` ⇒ `Instantiated H m s.abs imports s'.abs inst`.
- T5 memory (`Chunks`): `get_set`, `byte_write`, `abs_read`, `abs_write` (funext under `Inv`), `writeBytes`/`readBytes`, `grow_none`/`grow_some` (= `MemInst.grow`), `alloc_abs`; `fill`, `copy` (both overlap directions) and `init` loops = the stepper's whole expansion (`fill_loop`, `copy_up_loop`, `copy_down_loop`, `init_loop`).
- T3 `machineRun_must` → U27 (the `Must`/`SysMust` bridge lands with the system layer it serves).

## Runner (glue, `FVATest/Spec.lean`)
- Every action, initialization and uninstantiable check runs on the machine; the store persists in machine form; the stepper runner's snapshot scheme is gone.
- `FVA_SPEC_OUTCOMES` per-command outcomes = the stepper runner's on all 82 scripts except `memory_copy`'s executed commands (all 82 trace files byte-identical: 27,373 command rows, memory_copy then validation-only on both; tallies sha256-equal); characterization goldens (`scripts/test-char`) regenerated with that diff alone + U25's.
- `memory_copy` = 4450/0/0 (D30 accounting); fast + full modes execute it (fast-gate ruling: 10 s of a 12.7 s `--fast` suite, slowest script); the validation-only knob (`FVA_SPEC_VALIDATE_ONLY`) is gone.

## Evidence
- E1 official scripts through the machine, every pin exact: `scripts/test-spec` full 14 s, `--fast` 12.7 s, `memory_copy` 10–13 s (desktop, 4 workers; the stepper runner: ≈ 5 min full, memory_copy > 900 s); the nixbox wall (< 300 s acceptance) = the full gate's spec step.
- E2 per-command outcomes equal (Runner); difftest unchanged (its evaluator is not the machine).
- E3 planted (each patched, built, restored byte-identically): `brPop` popping `take (n + 1)` values → `FVA/Proof/Exec/Machine.lean:180` unsolved goals (`seq_wrap_br`); `MMem.copy` reading the destination → errors at `:1107`/`:1112` (`stepPlain_sim`, copy case).
- E4 performance protocol (frozen here, run in U29d): workload = complete machine states (`decide`/defeq of the whole next state, not a projection) from the D28 bustools run (≥ 1 MB memory, ≥ 1,000 functions: early, middle and late states, deep frames, bulk overlap, large addresses) + the compiled `memory_copy` wall; measured = kernel s/step, KB/step, export bytes per segment, each replay kernel's wall + RSS; variants = leaf width `W` ∈ {5, 6, 8} (one-line change: proofs are generic in `W`); value representation stays `Val` unless dispatch dominates. Reason for U29d: the workload states exist only once U27 + U29c run bustools, and U29d builds the checkpoint generator the protocol measures through.
- E5 mutation: `FVA/Impl/Exec/{Chunks,Machine}.lean` in the `fvamut` exec group (`--update` before the commit).

## Out of scope
- `run_complete` / must-adequacy (U4 deferral stands: the machine serves concrete runs; symbolic proofs stay on the stepper, engine C).
- EH, tail calls, typed refs (U28d); host calls, the system layer, WASI (U27, U29).
- Certificate/checkpoint format + versioned machine-state boundary (U29d) beyond keeping `MState` data-only and printable.
