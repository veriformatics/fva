# spike-v — U20 arm V

S1–S5 = Lean-checked, standard axioms only; five ordered stage commits. Default independent replay + fixed-CPU cost measurements = MAIN-owned, not run by this arm. No method-superiority claim.

- Worktree: `/home/eturkes/Projects/fva/.scratch/worktrees/spike-v` (`wt/spike-v`); base `c736868`; final `14f50a9`; working tree clean.
- Start: 2026-11-01T10:50:24+09:00; budget deadline: 2026-11-01T18:50:24+09:00. Last frozen-root first success: 2026-11-01T14:55:50+09:00; final commit: 2026-11-01T15:00:36+09:00.
- File paths in the declaration table are relative to the worktree above.

## Per statement

M0 end = first successful build of the frozen root, not cleanup/commit. Build counts include infrastructure builds + diagnostic Lean probes; later smoke checks are shown separately. M1 statement-specific = retained source added in that stage. Infrastructure-used cells count source declarations reached by that root's kernel-dependency graph, split by first authoring stage; tactic code/module commands are outside that graph and are charged in the full M1 table below.

| stmt | status | theorem name | start (ISO time) | end (ISO time) | build iterations | statement-specific code lines | infrastructure lines used (new / reused) | `#print axioms` | failure class if not completed + last failed obligation + command/rc |
|---|---|---|---|---|---|---|---|---|---|
| S1 MemcpyS1 | proved (`61d7156`) | `Subjects.Lz4C.SpikeV.s1` | 2026-11-01T10:50:24+09:00 | 2026-11-01T11:59:40+09:00 | 42 to first success; 44 incl cleanup/smoke | 312 | 151 / 0 | `[propext, Classical.choice, Quot.sound]` | none; final root + local-get smoke rc 0 |
| S2 MemmoveS2 | proved (`5dd241e`) | `Subjects.Lz4C.SpikeV.s2` | 2026-11-01T12:03:27+09:00 | 2026-11-01T12:40:28+09:00 | 16 | 649 | 120 / 151 | `[propext, Classical.choice, Quot.sound]` | none; final root rc 0 |
| S3 LitWildS3 | proved (`dfb107e`) | `Subjects.Lz4C.SpikeV.s3` | 2026-11-01T12:40:50+09:00 | 2026-11-01T13:04:42+09:00 | 14 | 13 | 160 / 151 | `[propext, Classical.choice, Quot.sound]` | none; root + callee-contract smoke rc 0 |
| S4 MatchWildS4 | proved (`a1c9e63`) | `Subjects.Lz4C.SpikeV.s4` | 2026-11-01T13:05:24+09:00 | 2026-11-01T13:09:56+09:00 | 2 | 119 | 0 / 218 | `[propext, Classical.choice, Quot.sound]` | none; final root rc 0 |
| S5 ShortcutS5 | proved (`14f50a9`) | `Subjects.Lz4C.SpikeV.s5` | 2026-11-01T13:10:17+09:00 | 2026-11-01T14:55:50+09:00 | 29 to first success; 31 incl two-call smoke/final import | 540 | 35 / 185 | `[propext, Classical.choice, Quot.sound]` | none; root + two-call smoke + all-root import/axiom check rc 0 |

`FinalCheck.lean` imports all five roots + package-boundary smokes. Its command/rc is in `S5-build-31.log`; every root and `calls_twice` prints exactly the three standard axioms above. `leanchecker`, `con-leche`, exporter size/time, replay size/time/RSS, fixed-CPU elaboration runs, `fva trust`, and `scripts/gate` were not run by this arm (the brief reserves them to MAIN or excludes them).

## Measurements and accounting

- Raw observations: `builds.tsv`, `S<k>-build-<i>.log`; `build` records start/end/rc on each invocation. Logs are complete; the terminal reporter filters them.
- M0 tool-use counts: transcript `tool_use` blocks within each inclusive, second-resolution M0 interval. Parallel child calls are separate blocks in this transcript. Includes orientation, measurements/reporting performed while builds ran, and waits; not a pure typing-time estimate.

| stage | M0 elapsed (s) | tool-use blocks |
|---|---:|---:|
| S1 | 4156 | 196 |
| S2 | 2221 | 58 |
| S3 | 1432 | 45 |
| S4 | 272 | 10 |
| S5 | 6333 | 142 |

- Counter = the committed `FVA.Trust.codeLines` implementation, called by `Measure.lean`. `metrics-src/<stage>/` contains `git show` snapshots of each checkpoint's changed source. Final source: 37 files, 198 source declarations, **2448 code lines**. Declaration lines + module-command rows reconcile to 2448.
- Full M1 cost counts all retained source, including tactic metaprograms, module commands, smokes and reused-text adaptations. Infrastructure = parameterized WP/control rules, tactics, Nat/memory facts, and the generic wildcopy/rank template; concrete binary code/layout, decoder-specific exits and frozen roots = statement-specific. Roles are listed per declaration below.
- S2's forward-code/proof files were mechanically adapted from this arm's own S1 (`make-forward.pl`); S4's rank proof from this arm's own S3 (`make-s4.pl`). They are conservatively charged as statement-specific handwritten source, not discounted as generated output. Lean-generated constructors/recursors/equation auxiliaries are grouped under their owning source declaration; they add no handwritten source lines.
- The full-cost table is independent of role labels. Stage 5 includes the five-code-line increase to the earlier `Modular.lean`; the rest of that module is carried source. Existing FVA/Lean/Mathlib source is the common baseline, not new arm source.

| stage | new/changed net source lines | statement-specific added | infrastructure added | earlier infrastructure carried | cumulative source lines |
|---|---:|---:|---:|---:|---:|
| S1 | 553 | 312 | 241 | 0 | 553 |
| S2 | 778 | 649 | 129 | 241 | 1331 |
| S3 | 335 | 13 | 322 | 370 | 1666 |
| S4 | 119 | 119 | 0 | 692 | 1785 |
| S5 | 663 | 540 | 123 | 692 | 2448 |


The per-statement infrastructure-used cells are a different, narrower observation: `Deps.lean` traverses owned declarations by module origin, including private/generated helpers; `render-metrics.pl` maps them to source declarations. Every owned dependency maps (positive control: root `s5` maps once; unmapped constants = 0). It excludes tactic execution and non-declaration commands. Raw mapping = `deps.tsv`, `root-source-use.tsv`; no source-use claim is made for every carried line.

M4: S2/S1 statement-specific source = 649/312 = 2.080; M0 = 2221/4156 = 0.534 (static instructions: 191/93). S4/S3 statement-specific source = 119/13 = 9.154; M0 = 272/1432 = 0.190. The S4 line ratio is sensitive to role assignment: S3 pays for 322 generic infrastructure lines, while S4's new exit/rank adapter is decoder-specific. Whole-stage source S4/S3 = 119/335 = 0.355. Both partitions are exposed; selection must use the contract's full cost vector, not a role-sensitive scalar.

M2/M3 remain unconfirmed: this arm's ordinary build durations are diagnostics, not the prescribed interleaved fixed-CPU, prebuilt-import measurement. MAIN must replay both default checkers and assess the resource bound before eligibility is established.

## Files and declarations

Retained source declarations, not every kernel-generated auxiliary constant. The anonymous WP instance is named by its actual environment name. Tactic rows use their source syntax name. Module commands are separate rows so totals include imports, scopes, attributes, options and axiom checks.

| file | declaration | kind | code lines (comments + blank lines excluded) |
|---|---|---|---:|
| `FVA/Proof/Lib/WasmStructuralWP.lean:9` | `FVA.Wasm.Exec.VC.Spec.focusLabel` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmStructuralWP.lean:14` | `FVA.Wasm.Exec.VC.Spec.unfocusLabel` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmStructuralWP.lean:19` | `FVA.Wasm.Exec.VC.Spec.focusFrame` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmStructuralWP.lean:24` | `FVA.Wasm.Exec.VC.Spec.unfocusFrame` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmStructuralWP.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 5 |
| `FVA/Proof/Lib/WasmWP.lean:16` | `FVA.Wasm.Exec.VC.Region` | infrastructure | 1 |
| `FVA/Proof/Lib/WasmWP.lean:18` | `FVA.Wasm.Exec.VC.Program` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmWP.lean:23` | `FVA.Wasm.Exec.VC.instWPProgramConfigPropEStackEnd` | infrastructure | 10 |
| `FVA/Proof/Lib/WasmWP.lean:35` | `FVA.Wasm.Exec.VC.sound` | infrastructure | 3 |
| `FVA/Proof/Lib/WasmWP.lean:39` | `FVA.Wasm.Exec.VC.Spec.cut` | infrastructure | 3 |
| `FVA/Proof/Lib/WasmWP.lean:43` | `FVA.Wasm.Exec.VC.Spec.finish` | infrastructure | 3 |
| `FVA/Proof/Lib/WasmWP.lean:47` | `FVA.Wasm.Exec.VC.Spec.blocked` | infrastructure | 1 |
| `FVA/Proof/Lib/WasmWP.lean:49` | `FVA.Wasm.Exec.VC.next` | infrastructure | 5 |
| `FVA/Proof/Lib/WasmWP.lean:55` | `FVA.Wasm.Exec.VC.Spec.step` | infrastructure | 12 |
| `FVA/Proof/Lib/WasmWP.lean:69` | `FVA.Wasm.Exec.VC.Spec.contract` | infrastructure | 4 |
| `FVA/Proof/Lib/WasmWP.lean:77` | `FVA.Wasm.Exec.VC.wasm_vcgen` | infrastructure | 37 |
| `FVA/Proof/Lib/WasmWP.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/Align.lean:7` | `Subjects.Lz4C.SpikeV.nat_mask4` | infrastructure | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/Align.lean:19` | `Subjects.Lz4C.SpikeV.mask4` | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/Align.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/Attr.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Calls.lean:8` | `Subjects.Lz4C.SpikeV.call_memcpy` | infrastructure | 30 |
| `FVATest/Subjects/Lz4C/SpikeV/Calls.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/CallsSmoke.lean:11` | `Subjects.Lz4C.SpikeV.call_smoke` | infrastructure | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/CallsSmoke.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/CallsTwice.lean:12` | `Subjects.Lz4C.SpikeV.call_once8` | infrastructure | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/CallsTwice.lean:24` | `Subjects.Lz4C.SpikeV.calls_twice` | infrastructure | 30 |
| `FVATest/Subjects/Lz4C/SpikeV/CallsTwice.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:7` | `Subjects.Lz4C.SpikeV.byteBody` | S1-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:14` | `Subjects.Lz4C.SpikeV.fourBody` | S1-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:30` | `Subjects.Lz4C.SpikeV.middleBody` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:36` | `Subjects.Lz4C.SpikeV.outerBody` | S1-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:44` | `Subjects.Lz4C.SpikeV.memcpy_code` | S1-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:47` | `Subjects.Lz4C.SpikeV.memcpy_defaults` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:49` | `Subjects.Lz4C.SpikeV.memcpy_locals` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:51` | `Subjects.Lz4C.SpikeV.funcCode` | S1-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:55` | `Subjects.Lz4C.SpikeV.outerCode` | S1-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:59` | `Subjects.Lz4C.SpikeV.byteHead` | S1-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:62` | `Subjects.Lz4C.SpikeV.fourHead` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean:68` | `Subjects.Lz4C.SpikeV.fourAfter` | S1-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/CopyCode.lean` | module commands (imports/scopes/attributes/axiom checks) | S1-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MemcpyLoop.lean:11` | `Subjects.Lz4C.SpikeV.memcpy_zero` | S1-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/MemcpyLoop.lean:22` | `Subjects.Lz4C.SpikeV.byte_iter` | S1-specific | 21 |
| `FVATest/Subjects/Lz4C/SpikeV/MemcpyLoop.lean:46` | `Subjects.Lz4C.SpikeV.byte_loop` | S1-specific | 35 |
| `FVATest/Subjects/Lz4C/SpikeV/MemcpyLoop.lean:84` | `Subjects.Lz4C.SpikeV.four_iter` | S1-specific | 32 |
| `FVATest/Subjects/Lz4C/SpikeV/MemcpyLoop.lean` | module commands (imports/scopes/attributes/axiom checks) | S1-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:10` | `Subjects.Lz4C.SpikeV.fwd_zero` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:12` | `Subjects.Lz4C.SpikeV.fwd_succ` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:16` | `Subjects.Lz4C.SpikeV.write_size` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:18` | `Subjects.Lz4C.SpikeV.fwd_size` | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:23` | `Subjects.Lz4C.SpikeV.fwd_pos` | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:30` | `Subjects.Lz4C.SpikeV.fwd_add` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:38` | `Subjects.Lz4C.SpikeV.setMem_get` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:42` | `Subjects.Lz4C.SpikeV.setMem_get_map` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:46` | `Subjects.Lz4C.SpikeV.setMem_funcs` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:49` | `Subjects.Lz4C.SpikeV.setMem_setMem` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:55` | `Subjects.Lz4C.SpikeV.setMem_self` | infrastructure | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:65` | `Subjects.Lz4C.SpikeV.decide_true_of` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:68` | `Subjects.Lz4C.SpikeV.decide_false_of` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:71` | `Subjects.Lz4C.SpikeV.nat_toNat` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:74` | `Subjects.Lz4C.SpikeV.byte_toNat` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:78` | `Subjects.Lz4C.SpikeV.nat_iadd` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:81` | `Subjects.Lz4C.SpikeV.nat_ilt` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:85` | `Subjects.Lz4C.SpikeV.nat_ine` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:89` | `Subjects.Lz4C.SpikeV.nat_eqz` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:93` | `Subjects.Lz4C.SpikeV.ofNat_eq_zero` | infrastructure | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:103` | `Subjects.Lz4C.SpikeV.nat_pred` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:111` | `Subjects.Lz4C.SpikeV.nat_decr` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:115` | `Subjects.Lz4C.SpikeV.one_range` | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:124` | `Subjects.Lz4C.SpikeV.mask3` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean:132` | `Subjects.Lz4C.SpikeV.access_store8` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/Memory.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 12 |
| `FVATest/Subjects/Lz4C/SpikeV/Modular.lean:10` | `Subjects.Lz4C.SpikeV.wasm_modular` | infrastructure | 105 |
| `FVATest/Subjects/Lz4C/SpikeV/Modular.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:7` | `Subjects.Lz4C.SpikeV.vMinus` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:9` | `Subjects.Lz4C.SpikeV.minus_one` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:15` | `Subjects.Lz4C.SpikeV.minus_four` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:21` | `Subjects.Lz4C.SpikeV.minus_nat` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:25` | `Subjects.Lz4C.SpikeV.add_minus` | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:32` | `Subjects.Lz4C.SpikeV.nat_sub_add` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean:35` | `Subjects.Lz4C.SpikeV.add_add_sub` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveArith.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveByte.lean:11` | `Subjects.Lz4C.SpikeV.MoveBwd.byte_iter` | S2-specific | 24 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveByte.lean:38` | `Subjects.Lz4C.SpikeV.MoveBwd.byte_loop` | S2-specific | 42 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveByte.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:8` | `Subjects.Lz4C.SpikeV.MoveBwd.byteBody` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:15` | `Subjects.Lz4C.SpikeV.MoveBwd.fourBody` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:32` | `Subjects.Lz4C.SpikeV.MoveBwd.remBody` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:39` | `Subjects.Lz4C.SpikeV.MoveBwd.afterRem` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:45` | `Subjects.Lz4C.SpikeV.MoveBwd.backBody` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:50` | `Subjects.Lz4C.SpikeV.MoveBwd.memmove_code` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:54` | `Subjects.Lz4C.SpikeV.MoveBwd.memmove_locals` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:56` | `Subjects.Lz4C.SpikeV.MoveBwd.outerCode` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:61` | `Subjects.Lz4C.SpikeV.MoveBwd.byteHead` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:65` | `Subjects.Lz4C.SpikeV.MoveBwd.byteAfter` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean:68` | `Subjects.Lz4C.SpikeV.MoveBwd.fourHead` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveCode.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveForward.lean:12` | `Subjects.Lz4C.SpikeV.MoveFwd.after_four` | S2-specific | 12 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveForward.lean:25` | `Subjects.Lz4C.SpikeV.MoveFwd.four_tail` | S2-specific | 23 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveForward.lean:49` | `Subjects.Lz4C.SpikeV.MoveFwd.four_loop` | S2-specific | 57 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveForward.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFour.lean:11` | `Subjects.Lz4C.SpikeV.MoveBwd.four_iter` | S2-specific | 37 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFour.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:11` | `Subjects.Lz4C.SpikeV.MoveFwd.perm7` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:15` | `Subjects.Lz4C.SpikeV.MoveFwd.byteBody` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:22` | `Subjects.Lz4C.SpikeV.MoveFwd.fourBody` | S2-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:38` | `Subjects.Lz4C.SpikeV.MoveFwd.middleBody` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:44` | `Subjects.Lz4C.SpikeV.MoveFwd.outerBody` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:52` | `Subjects.Lz4C.SpikeV.MoveFwd.funcCode` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:56` | `Subjects.Lz4C.SpikeV.MoveFwd.outerCode` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:60` | `Subjects.Lz4C.SpikeV.MoveFwd.byteHead` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:63` | `Subjects.Lz4C.SpikeV.MoveFwd.fourHead` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean:69` | `Subjects.Lz4C.SpikeV.MoveFwd.fourAfter` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdCode.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdLoop.lean:11` | `Subjects.Lz4C.SpikeV.MoveFwd.byte_iter` | S2-specific | 21 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdLoop.lean:34` | `Subjects.Lz4C.SpikeV.MoveFwd.byte_loop` | S2-specific | 35 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdLoop.lean:71` | `Subjects.Lz4C.SpikeV.MoveFwd.four_iter` | S2-specific | 32 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveFwdLoop.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:7` | `Subjects.Lz4C.SpikeV.bwdCopy` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:11` | `Subjects.Lz4C.SpikeV.mem_ext` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:19` | `Subjects.Lz4C.SpikeV.write_copy_byte` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:27` | `Subjects.Lz4C.SpikeV.move_zero` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:33` | `Subjects.Lz4C.SpikeV.fwd_move` | infrastructure | 26 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:60` | `Subjects.Lz4C.SpikeV.bwd_size` | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:65` | `Subjects.Lz4C.SpikeV.bwd_move` | infrastructure | 24 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:90` | `Subjects.Lz4C.SpikeV.bwd_add` | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean:99` | `Subjects.Lz4C.SpikeV.bwd_prefix_pos` | infrastructure | 13 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveMemory.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/MovePrefix.lean:11` | `Subjects.Lz4C.SpikeV.memmove_zero` | S2-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/MovePrefix.lean:23` | `Subjects.Lz4C.SpikeV.memmove_forward_prefix` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeV/MovePrefix.lean:40` | `Subjects.Lz4C.SpikeV.memmove_backward_prefix` | S2-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeV/MovePrefix.lean:56` | `Subjects.Lz4C.SpikeV.memmove_backward_join` | S2-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/MovePrefix.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveTotal.lean:11` | `Subjects.Lz4C.SpikeV.MoveBwd.four_loop` | S2-specific | 46 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveTotal.lean:64` | `Subjects.Lz4C.SpikeV.memmove_backward_tail` | S2-specific | 26 |
| `FVATest/Subjects/Lz4C/SpikeV/MoveTotal.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 12 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean:12` | `Subjects.Lz4C.SpikeV.after_four` | S1-specific | 12 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean:25` | `Subjects.Lz4C.SpikeV.memcpy_prefix` | S1-specific | 17 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean:46` | `Subjects.Lz4C.SpikeV.four_tail` | S1-specific | 23 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean:70` | `Subjects.Lz4C.SpikeV.four_loop` | S1-specific | 57 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean:131` | `Subjects.Lz4C.SpikeV.s1` | S1-specific | 25 |
| `FVATest/Subjects/Lz4C/SpikeV/S1.lean` | module commands (imports/scopes/attributes/axiom checks) | S1-specific | 13 |
| `FVATest/Subjects/Lz4C/SpikeV/S2.lean:10` | `Subjects.Lz4C.SpikeV.s2` | S2-specific | 62 |
| `FVATest/Subjects/Lz4C/SpikeV/S2.lean` | module commands (imports/scopes/attributes/axiom checks) | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/S3.lean:11` | `Subjects.Lz4C.SpikeV.loop_branch` | infrastructure | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/S3.lean:21` | `Subjects.Lz4C.SpikeV.lit_one` | infrastructure | 25 |
| `FVATest/Subjects/Lz4C/SpikeV/S3.lean:47` | `Subjects.Lz4C.SpikeV.lit_total` | infrastructure | 59 |
| `FVATest/Subjects/Lz4C/SpikeV/S3.lean:107` | `Subjects.Lz4C.SpikeV.s3` | S3-specific | 10 |
| `FVATest/Subjects/Lz4C/SpikeV/S3.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:11` | `Subjects.Lz4C.SpikeV.matchLoop_code` | S4-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:14` | `Subjects.Lz4C.SpikeV.body4_tail` | S4-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:16` | `Subjects.Lz4C.SpikeV.ctx5_fill` | S4-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:20` | `Subjects.Lz4C.SpikeV.match_branch` | S4-specific | 10 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:31` | `Subjects.Lz4C.SpikeV.match_one` | S4-specific | 26 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:58` | `Subjects.Lz4C.SpikeV.match_total` | S4-specific | 59 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean:118` | `Subjects.Lz4C.SpikeV.s4` | S4-specific | 10 |
| `FVATest/Subjects/Lz4C/SpikeV/S4.lean` | module commands (imports/scopes/attributes/axiom checks) | S4-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/S5.lean:10` | `Subjects.Lz4C.SpikeV.s5` | S5-specific | 125 |
| `FVATest/Subjects/Lz4C/SpikeV/S5.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortAttr.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:7` | `Subjects.Lz4C.SpikeV.shortTail5` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:8` | `Subjects.Lz4C.SpikeV.shortTail6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:9` | `Subjects.Lz4C.SpikeV.shortTail7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:10` | `Subjects.Lz4C.SpikeV.shortTail8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:12` | `Subjects.Lz4C.SpikeV.shortBody` | S5-specific | 24 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:37` | `Subjects.Lz4C.SpikeV.mainLoop_code` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:39` | `Subjects.Lz4C.SpikeV.shortBody5` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:43` | `Subjects.Lz4C.SpikeV.shortBody6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:44` | `Subjects.Lz4C.SpikeV.shortBody7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:45` | `Subjects.Lz4C.SpikeV.shortBody8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:47` | `Subjects.Lz4C.SpikeV.shortCtx6` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:49` | `Subjects.Lz4C.SpikeV.shortCtx7` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean:51` | `Subjects.Lz4C.SpikeV.shortCtx8` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCode.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:12` | `Subjects.Lz4C.SpikeV.shortCopy1Rest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:13` | `Subjects.Lz4C.SpikeV.shortCopy2Rest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:14` | `Subjects.Lz4C.SpikeV.shortCopy3Rest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:15` | `Subjects.Lz4C.SpikeV.shortDoneRest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:17` | `Subjects.Lz4C.SpikeV.short_good` | S5-specific | 14 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:32` | `Subjects.Lz4C.SpikeV.short_copy1` | S5-specific | 17 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:50` | `Subjects.Lz4C.SpikeV.short_copy2` | S5-specific | 19 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:70` | `Subjects.Lz4C.SpikeV.short_copy3` | S5-specific | 19 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean:90` | `Subjects.Lz4C.SpikeV.short_finish` | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortCopies.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 13 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortLiteral.lean:11` | `Subjects.Lz4C.SpikeV.shortLocals` | S5-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortLiteral.lean:17` | `Subjects.Lz4C.SpikeV.shortMatchCode` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortLiteral.lean:21` | `Subjects.Lz4C.SpikeV.short_literal` | S5-specific | 25 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortLiteral.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortMatch.lean:11` | `Subjects.Lz4C.SpikeV.short_ml15` | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortMatch.lean:19` | `Subjects.Lz4C.SpikeV.short_off8` | S5-specific | 9 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortMatch.lean:29` | `Subjects.Lz4C.SpikeV.short_match_bad` | S5-specific | 14 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortMatch.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 10 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:11` | `Subjects.Lz4C.SpikeV.shortNest` | S5-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:18` | `Subjects.Lz4C.SpikeV.shortCfg` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:21` | `Subjects.Lz4C.SpikeV.tokenLocals` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:24` | `Subjects.Lz4C.SpikeV.shortTokenRest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:26` | `Subjects.Lz4C.SpikeV.shortCopyRest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:28` | `Subjects.Lz4C.SpikeV.shortMatchRest` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean:30` | `Subjects.Lz4C.SpikeV.short_token` | S5-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortPoints.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean:11` | `Subjects.Lz4C.SpikeV.shortTokenCode` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean:15` | `Subjects.Lz4C.SpikeV.short_ll15` | S5-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean:22` | `Subjects.Lz4C.SpikeV.short_src_fail` | S5-specific | 10 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean:33` | `Subjects.Lz4C.SpikeV.short_dst_fail` | S5-specific | 14 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean:48` | `Subjects.Lz4C.SpikeV.short_room` | S5-specific | 13 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortRooms.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 11 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSuccess.lean:11` | `Subjects.Lz4C.SpikeV.short_success` | S5-specific | 68 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSuccess.lean` | module commands (imports/scopes/attributes/axiom checks) | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:24` | `Subjects.Lz4C.SpikeV.nat_ile` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:28` | `Subjects.Lz4C.SpikeV.nat_igt` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:32` | `Subjects.Lz4C.SpikeV.shift4` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:36` | `Subjects.Lz4C.SpikeV.mask15` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:44` | `Subjects.Lz4C.SpikeV.sub_nat` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:48` | `Subjects.Lz4C.SpikeV.sub_bits` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:50` | `Subjects.Lz4C.SpikeV.read_two` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:54` | `Subjects.Lz4C.SpikeV.fwd_byte_outside` | infrastructure | 8 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:63` | `Subjects.Lz4C.SpikeV.fwd_join` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:67` | `Subjects.Lz4C.SpikeV.sub_value_nat` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:71` | `Subjects.Lz4C.SpikeV.short_updates` | S5-specific | 13 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:85` | `Subjects.Lz4C.SpikeV.set_same` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:91` | `Subjects.Lz4C.SpikeV.after_lit1` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:92` | `Subjects.Lz4C.SpikeV.after_lit2` | infrastructure | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:94` | `Subjects.Lz4C.SpikeV.shortOffset` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:97` | `Subjects.Lz4C.SpikeV.offset_fold` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean:101` | `Subjects.Lz4C.SpikeV.shortOffset_lt` | S5-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/ShortSupport.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 22 |
| `FVATest/Subjects/Lz4C/SpikeV/Smoke.lean:9` | `Subjects.Lz4C.SpikeV.local_get_smoke` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/Smoke.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:11` | `Subjects.Lz4C.SpikeV.wildBody` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:17` | `Subjects.Lz4C.SpikeV.wildLocals` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:20` | `Subjects.Lz4C.SpikeV.wildLocals_twice` | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:25` | `Subjects.Lz4C.SpikeV.litLoop_code` | S3-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:27` | `Subjects.Lz4C.SpikeV.litEntry_code` | S3-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean:30` | `Subjects.Lz4C.SpikeV.wild_prefix` | infrastructure | 22 |
| `FVATest/Subjects/Lz4C/SpikeV/Wild.lean` | module commands (imports/scopes/attributes/axiom checks) | infrastructure | 8 |


## Engine notes

### E1 — representation and soundness

`Program.exec H R W depth C st f code` is a configuration-oriented Wasm program. Normal value = `Config`; assertion lattice = `Prop`; exception stack = empty. Wasm labels/frames retain `br`/`return`; the arm adds no second control-flow semantics. WP denotes **`Until H (Within R W) Q (C.fill cfg)`** directly: total arrival, all `Step` successors, per-step footprint strictly before the exit.

`depth` bounds VC-generation prefixes, not semantic execution. A callee contract may discharge an arbitrarily long execution at one call site. `sound` extracts the frozen `Until` form from a triple. `Spec.step` is the only instruction-step soundness bridge: `until_context_seq` + stepper uniqueness + checked access. Its sole direct-step occurrence is `FVA/Proof/Lib/WasmWP.lean:65`. Statement files contain no `wasm_cstepu`, `until_context_seq`, `wasm_step1`, or equivalent direct-step tactic call.

`wasm_vcgen` invokes Lean 4.35 `vcgen` one spec pass at a time, then normalizes the reference-stepper/access discriminants with the existing `wasm_step`/`wasm_access` sets. This bridge is needed because vcgen's equation database rewrites programs, not arbitrary nested stepper discriminants. `Spec.finish` closes a prefix only after its postcondition is proved.

`wasm_modular` adds checked focus/unfocus triples: both sides are **the identical configuration**, so these are representation changes, not ghost execution steps. Real branch/admin reductions still use `Spec.step`. `call_memcpy` wraps S1 as a WP spec, widens the footprint by proved containment, and never unfolds the callee at callers. Its address/closure binding is explicit.

### E2 — what the next function's author writes

- **Per block:** actual code slice or a `kernel_rfl`-checked slice equation; entry facts; an exact join-point assertion; the arithmetic/memory facts for its VCs. Run `wasm_vcgen` or `wasm_modular` with those facts. The output obligations are uniqueness, access containment, local bounds and the post-state.
- **Per loop:** entry invariant + decreasing Nat rank, one vcgen-checked iteration contract, and the induction/composition. The template is ordinary Lean, not an invariant inference engine.
- **Per call:** prove the callee once, register/wrap its total WP contract, supply lookup/closure/memory facts and footprint containment. For several calls that change memory, this arm's successful interface uses explicit **single-call block contracts** and `Until.trans`; their memory summaries are joined by `fwd_add`.

### E3 — statement mechanisms and reuse

- S1: vcgen for zero path, entry/exit adapters and byte/four-byte iteration contracts; decreasing Nat induction for both loops; exact ascending `fwdCopy`, including forward overlap.
- S2: the same mechanism for four loops. Own S1 forward proof text adapted to func4's locals; kernel AST equality rejected the naive uniform local permutation because original `n` stays in local2 before the loop. Fixed that seam. Separate proofs show ascending copy = snapshot copy when `d ≤ s`, descending copy = snapshot copy when `s ≤ d`; address zero is supported by wrap-safe pointer lemmas.
- S3: generic `wild_prefix` calls S1; branch adapter + ranked chunk induction. `q=e` takes the required single do-while iteration.
- S4: `wild_prefix` reused unchanged with other locals and `br 1`; a new adapter catches that branch at the real main-loop label; rank text adapted from own S3. No engine addition.
- S5: explicit token, room, offset and match join-point contracts; all five frozen exits. Literal call = 16 bytes. Successful match = three vcgen-checked single-call blocks (8+8+2) + branch-back adapter; exact memory summaries joined by `fwd_add`. Source-offset bytes are proved unchanged by the disjoint literal write. All 19 locals match `ShortExit` exactly; no source/proof statement was weakened.

**Direct-stepping fallback: none.** `Until.trans`/`mono`, rank induction and callee-contract application are composition, not instruction stepping.

### E4 — failed approaches and limits

- S5's monolithic disjunctive postcondition exhausted 4M heartbeats in simp/acLt (283 s; `S5-build-3.log`, rc 1). A directed-update variant still expanded poorly and was stopped at 548 s (`S5-build-4.log`, Lean rc 143 / Lake rc 1). Explicit join-point contracts replaced it. The original attribution to local-update sorting was not established; removing that sorter alone did not solve the monolithic attempt.
- Multi-call vcgen inference selected the original memory and produced **rejected** obligations such as `fwdCopy mem … 8 = mem` (`S5-build-14.log`, `S5-build-18.log`, rc 1). Explicit snapshot-binding experiments then hit elaboration recursion. They were removed. The retained solution composes single-call triples over abstract current memories; `calls_twice` checks that composition at the package boundary.
- Retained driver repairs: normalize the initial program before dispatch; resolve lookup premises before normalizing the continuation. Retained proof optimization: `fwdCopy` is **locally irreducible** for larger symbolic copies, while its transparent definition and the frozen statement stay unchanged. No `opaque` declaration is added.
- Failed revisions were not separately committed. Complete logs retain command/rc/timestamps; a monolithic source excerpt is retained, while its support files evolved. The five **successful** stage checkpoints are committed and replayable.
- Next reusable work: package join-point/single-call contracts and their memory parameters as a first-class interface; build a directed local-update normalizer; keep copying summaries symbolic. The current engine exposes concrete frame/label geometry and requires the agent to reconstruct invariants. S5 is bounded readiness for this slice, not a proof of full-decoder scalability.

### E5 — verification scope

Passed: all five frozen root builds; final combined import + axiom closure check; local-get, under-label callee, and composed-two-call proof smokes; `git diff --check`; source-role/line reconciliation; owned-dependency mapping; frozen-scope scan; prohibited-construct scan; direct-step-boundary scan; report validator (planted table-cell failure rc 1, completed report rc 0).

- Prohibited-construct scan: planted control expected 2, actual 2, rc 0; arm `.lean` sources 0 matches, rc 1 (`forbidden-scan.log`). Includes `sorry`, new axioms, `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`, `debug.skipKernelTC`.
- Frozen scope: control expected one changed WP source, actual one; frozen `Spec`, Copy/Short/Code/Ext/O1/Instance/Model paths 0 changes, rc 0 (`frozen-scope.log`).
- Mechanism scan: expected one `until_context_seq` occurrence in generic soundness, actual one, rc 0; statement/support files 0 direct-step matches, rc 1 (`statement-stepping-scan.log`).
- LSP probe: no Lean server configured (`No LSP server available for file type: .lean`); compiler diagnostics used. Unused-tactic/parameter warnings remain; builds pass.
- No sampling in retained-source accounting, axiom closure or source/scope scans. Failed-build diagnosis read bounded excerpts; full logs are retained.

Not run: default checker replay (`leanchecker`, `con-leche`), export/replay/RSS metrics, prescribed M2 fixed-CPU runs, `fva trust`, full/fast gate. No claim that these pass. Scope is S1–S5, not full decoder R1–R3. Notify-set edits: none.

### E6 — raw inputs / regeneration

All paths below are in `/home/eturkes/Projects/fva/.scratch/u19c2/spike-v/`:

- `build`, `builds.tsv`, stage logs, `FinalCheck.lean`.
- `report-template.txt`, `build-report.pl`, `validate-report`, `validator-control.txt` (the planted invalid report).
- `Measure.lean`, `code-lines.tsv`, `stage-code-lines.tsv`, `stage-files.tsv`, `metrics-src/`, `render-metrics.pl`, `declaration-table.txt`, `m1-table.txt`.
- `Deps.lean`, `deps.tsv`, `root-source-use.tsv` (module-origin filtered graph, source-parent grouping).
- `tool-calls.tsv` (the M0 intervals above); transcript resolved with `context-gauge -p spike-v`, timestamps floored to seconds and tool-use blocks counted inclusively.
- `make-forward.pl`, `make-s4.pl` (own-text adaptations), diagnostic `.lean` probes, scan logs/controls, `S5-monolithic.lean` excerpt.

Regenerate final source counts from the worktree with `lake env lean --run <scratch>/Measure.lean FVA/Proof/Lib/WasmWP.lean FVA/Proof/Lib/WasmStructuralWP.lean FVATest/Subjects/Lz4C/SpikeV/*.lean`. The same counter on `metrics-src/` yields checkpoint costs. Run `lake env lean <scratch>/Deps.lean`, then `perl <scratch>/render-metrics.pl <scratch>` for source-use/detail tables. These accounting helpers are scratch-local inputs, not a shipped project gate.

## Statement issues

None found. All five frozen statements were proved as written. Their input-domain assumptions remain intact; in S5 the destination lower bound plus the 16-bit offset bound is what makes the match-pointer subtraction non-wrapping.

spike-v-DONE-1
