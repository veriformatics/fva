# spike-d — U20 arm d report

Arm start = 2026-11-01T10:50:05+09:00. Deadline = 2026-11-01T18:50:05+09:00. Base = c736868; branch = wt/spike-d. Raw build observations = builds.tsv + build-*.log. S1 interval includes orientation + shared infrastructure.

Status `proved` = the theorem's frozen type accepted by Lean + its axiom audit. Independent default-checker replay, M2 controlled runs, M3 exports and the repository gate = not run by this arm; MAIN performs them after harvest. Frozen Copy.lean + Short.lean SHA-256 = the U20 contract's exact hashes (2 files, hash command rc 0).

M0 tool-use events, arm-only transcript and inclusive ISO-second windows through first success: S1 = 167, S2 = 69, S3 = 15, S4 = 3, S5 = 88 (`tool-counts.tsv`; second-boundary administrative calls may be included). The counting unit is each recorded `tool_use`, including individual parallel calls.

## Per statement
| stmt | status (proved / not completed) | theorem name | start (ISO time) | end (ISO time) | build iterations | statement-specific code lines | infrastructure lines used (new / reused) | `#print axioms` | failure class if not completed + last failed obligation + command/rc |
|---|---|---|---|---|---|---|---|---|---|
| S1 MemcpyS1 | proved | `Subjects.Lz4C.SpikeD.s1` | 2026-11-01T10:50:05+09:00 | 2026-11-01T11:36:51+09:00 | 37 incl. axiom-audit rebuild (36 to first success) | 222 | 283 / 0 | `[propext, Classical.choice, Quot.sound]` (`build-37.log`) | none |
| S2 MemmoveS2 | proved | `Subjects.Lz4C.SpikeD.s2` | 2026-11-01T11:41:08+09:00 | 2026-11-01T12:17:21+09:00 | 16 incl. warning-cleanup rebuild (15 to first success) | 568 | 70 / 283 inventory | `[propext, Classical.choice, Quot.sound]` (`build-52.log`) | none |
| S3 LitWildS3 | proved | `Subjects.Lz4C.SpikeD.s3` | 2026-11-01T12:19:58+09:00 | 2026-11-01T12:28:55+09:00 | 4 | 138 | 26 / 283 S1 inventory | `[propext, Classical.choice, Quot.sound]` (`build-57.log`) | none |
| S4 MatchWildS4 | proved | `Subjects.Lz4C.SpikeD.s4` | 2026-11-01T12:30:11+09:00 | 2026-11-01T12:31:35+09:00 | 1 | 27 | 7 / 309 infrastructure + 138 S3 support | `[propext, Classical.choice, Quot.sound]` (`build-58.log`) | none |
| S5 ShortcutS5 | proved | `Subjects.Lz4C.SpikeD.s5` | 2026-11-01T12:33:22+09:00 | 2026-11-01T13:32:51+09:00 | 15 incl. closing all-root recheck (14 to first success) | 287 | 55 new/changed / 309 S1+S3 inventory | `[propext, Classical.choice, Quot.sound]` (`build-72.log`, closing `build-73.log`) | none |

## Files and declarations
| file | declaration | kind (infrastructure / S1…S5-specific / generated) | code lines (comments + blank lines excluded) |
|---|---|---|---|
| `FVA/Proof/Lib/DirectAttr.lean` | `wasm_direct` | infrastructure | 1 |
| `FVA/Proof/Lib/DirectContext.lean` | `DirectContext` | infrastructure | 5 |
| `FVA/Proof/Lib/DirectContext.lean` | `DirectContext.fill` | infrastructure | 5 |
| `FVA/Proof/Lib/DirectContext.lean` | `DirectContext.seq` | infrastructure | 20 |
| `FVA/Proof/Lib/DirectContext.lean` | `DirectContext.access_fill` | infrastructure | 11 |
| `FVA/Proof/Lib/DirectContext.lean` | `within_direct_fill` | infrastructure | 9 |
| `FVA/Proof/Lib/DirectContext.lean` | `until_direct_context_seq` | infrastructure | 8 |
| `FVA/Proof/Lib/Direct.lean` | `toNat32` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `add32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `sub32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `bool_true32` | infrastructure | 1 |
| `FVA/Proof/Lib/Direct.lean` | `bool_false32` | infrastructure | 1 |
| `FVA/Proof/Lib/Direct.lean` | `eq32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `ne32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `eqz32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `lt32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `le32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `gt32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `ge32` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `bitvec32_zero` | infrastructure | 5 |
| `FVA/Proof/Lib/Direct.lean` | `instrStep_load8` | infrastructure | 11 |
| `FVA/Proof/Lib/Direct.lean` | `instrStep_store8` | infrastructure | 10 |
| `FVA/Proof/Lib/Direct.lean` | `instrAccess_storePacked32` | infrastructure | 5 |
| `FVA/Proof/Lib/Direct.lean` | `instrAccess_store32` | infrastructure | 5 |
| `FVA/Proof/Lib/Direct.lean` | `read_byte` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `write_size` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `setMem_mems` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `setMem_funcs` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `setMem_length` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `setMem_twice` | infrastructure | 3 |
| `FVA/Proof/Lib/Direct.lean` | `setMem_self` | infrastructure | 6 |
| `FVA/Proof/Lib/Direct.lean` | `vals_append` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `vals_cons` | infrastructure | 2 |
| `FVA/Proof/Lib/Direct.lean` | `vals_nil` | infrastructure | 1 |
| `FVA/Proof/Lib/Direct.lean` | `"wasm_dstep"` | infrastructure | 36 |
| `FVA/Proof/Lib/Direct.lean` | `"wasm_drun"` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `fwd_size` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `fwd_zero` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `fwd_add` | S1-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `write_byte_toNat_lt` | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `and3` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `and_not3` | infrastructure | 13 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `ofNat_add_neg1` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/Memory.lean` | `add_neg1` | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyOuter` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyInner` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyFour` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyOne` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `oneBody` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyOne_eq` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `fourBody` | S1-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `copyFour_eq` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `one_loop` | S1-specific | 29 |
| `FVATest/Subjects/Lz4C/SpikeD/S1Loops.lean` | `four_loop` | S1-specific | 36 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `tailCode` | S1-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `returnCtx` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `outerCtx` | infrastructure | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `innerCtx` | S1-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `innerCode` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `outerCode` | S1-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `func3_code` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `copy_return` | infrastructure | 12 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `copy_outer_return` | infrastructure | 10 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `tail_loop` | S1-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeD/S1.lean` | `s1` | S1-specific | 87 |

| `FVATest/Subjects/Lz4C/SpikeD/S2Back.lean` | `backOne` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Back.lean` | `backFour` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Back.lean` | `back_one_loop` | S2-specific | 38 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Back.lean` | `back_four_loop` | S2-specific | 41 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `backRemainder` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `backEnd` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `moveBack` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `moveOuter` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `moveBackCtx` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `moveRemCtx` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `func4_code` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `move_back_end_core` | S2-specific | 47 |
| `FVATest/Subjects/Lz4C/SpikeD/S2End.lean` | `move_back_end` | S2-specific | 26 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `moveOne` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `moveFour` | S2-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `move_one_loop` | S2-specific | 29 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `move_four_loop` | S2-specific | 36 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `moveTail` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Forward.lean` | `move_tail_loop` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeD/S2ForwardPath.lean` | `moveInner` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2ForwardPath.lean` | `moveForward` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/S2ForwardPath.lean` | `moveInnerCtx` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S2ForwardPath.lean` | `move_forward_path` | S2-specific | 80 |
| `FVATest/Subjects/Lz4C/SpikeD/S2.lean` | `func4_locals` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S2.lean` | `s2` | S2-specific | 33 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `mem_ext` | infrastructure | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `write1_byte` | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `move_zero` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `move_forward_step` | S2-specific | 18 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `fwd_eq_move` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bwdCopy` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bwd_size` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `move_backward_step` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bwd_eq_move` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bwd_split` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `ofNat_bias` | infrastructure | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `ofNat_add_neg4` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bwd_tail_step` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Memory.lean` | `bias_add` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Remainder.lean` | `move_back_remainder_core` | S2-specific | 50 |
| `FVATest/Subjects/Lz4C/SpikeD/S2Remainder.lean` | `move_back_remainder` | S2-specific | 25 |

| `FVA/Proof/Lib/DirectCompose.lean` | `within_mono` | infrastructure | 4 |
| `FVA/Proof/Lib/DirectCompose.lean` | `Until.bindEq` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `memcpy_then` | S3-specific | 17 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `wildPost` | S3-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `wildBody` | S3-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `chunks_cover` | S3-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `chunks_one` | S3-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `chunks_succ` | S3-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `locals_pair` | S3-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `vI8_instr` | S3-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/Wild.lean` | `wild_loop` | S3-specific | 78 |
| `FVATest/Subjects/Lz4C/SpikeD/S3.lean` | `lit_entry` | S3-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S3.lean` | `s3` | S3-specific | 21 |

| `FVATest/Subjects/Lz4C/SpikeD/S4.lean` | `match_loop_eq` | S4-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S4.lean` | `s4` | S4-specific | 26 |

| `FVA/Proof/Lib/DirectMemory.lean` | `instrStep_loadU32` | infrastructure | 11 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter4` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter5` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortCode` | S5-specific | 24 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `short_main` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `short_body5` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `short_body6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `short_body7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `short_body8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortAfter4_nil` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortCtx` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Code.lean` | `shortCtx_fill` | S5-specific | 9 |
| `FVATest/Subjects/Lz4C/SpikeD/S5.lean` | `"short_steps"` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S5.lean` | `"short_norm"` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/S5.lean` | `s5` | S5-specific | 133 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Locals.lean` | `short_updates` | S5-specific | 12 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Locals.lean` | `short_repeat2` | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Match.lean` | `matchThreeCode` | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Match.lean` | `match_three` | S5-specific | 51 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `shr4` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `and15` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `fwd_byte_out` | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `fwd_source_byte` | S5-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `read_two` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/S5Memory.lean` | `literal_offset` | S5-specific | 10 |

## Engine notes (what an agent proving the next function writes per block, per loop, per call; what was hard; what you would build next)
Engine = reference-stepper `seq` rewrites, transported through `until_context_seq` / `until_direct_context_seq`; no instruction-list evaluator or WP. `wasm_dstep` proves the unique successor with `wasm_step` + `wasm_direct`, computes `Within` via `wasm_access`, closes non-memory accesses automatically and memory bounds by `omega`. `DirectContext` adds the caller's saved value stack to the existing labels/frames transport.

Per block: supply the named instruction slice + facts for locals/memory, then `iterate N wasm_dstep [...]`; split branch predicates in Lean. Per loop: write an induction on a decreasing natural counter + its continuation, numeric bounds and the memory-composition identity. Per call: instantiate the established `CopyCall` theorem, weaken its footprint and compose with `Until.trans`. S1 has two loop inductions (4-byte unroll and byte remainder), then caller-frame return glue.

S2 reuses S1's forward inductions by explicit, hand-written adaptation of the compiled local allocation; new descending inductions prove backward ordered copies, then memory extensionality identifies the appropriate ordered copy with snapshot `move`. Build 47 failed at `move_back_end` with kernel deep recursion (276.93 s, 20,825,812 KiB max RSS). Abstracting the wrapped `i32` bias values (`src − 4`, `dst − 4`) into parameters of `move_back_end_core`, with separate addition equalities, made the same end-path proof compile in 5.6 s (build 49; whole command 6.74 s, 2,684,720 KiB). These are authoring observations, not M2's controlled measurements. The attempted SIGTERM of build 47's compiler raced its completed exit (`No such process`); no process was killed then. Build 50 hit the same payload-growth pattern in the remainder composition and was terminated by observed PID: Lean rc 143, runner rc 1, 144.32 s, 22,817,616 KiB max RSS. `move_back_remainder_core` applies the same arbitrary-bias boundary; it compiles in 9.9 s (build 51). Builds 51 onward run under `MemoryMax=12G`, `MemorySwapMax=0`; no capped build exhausted it. Build 53 recompiles every S2 module warning-free, rc 0, 50.02 s total; the S2 module itself = 5.8 s. S2 added 638 exact source code lines: 568 statement-specific + 70 infrastructure/administration. `metrics-S2.tsv` + `declarations-S2.txt` retain the split. Reused infrastructure in the table = the existing stage-1 inventory, not a claim that every generic declaration is in the theorem's dependency closure.

S3 fixes the generic wildcopy body by local indices and an exit tail, proves `chunks`' ceiling arithmetic and an induction over the remaining chunks, and composes each `call 3` through S1. S4 instantiates that same theorem at locals 17/2/3 with exit tail `br 1`, then takes one branch step through the actual main-loop labels. No new loop invariant or call proof in S4. S3 → S4 reuse observations: 138 → 27 new statement-specific lines; 8m57s → 1m24s authoring interval. Counts conservatively classify all `Wild.lean` support as S3-specific even though the loop theorem is parameterized.

Hard point: `simp` unfolded the stepper's memory `Option.map` body before substituting its memory argument; this left symbolic guard terms in successor components. Pre-order, proved `instrStep_load8` / `instrStep_store8` equations remove that bookkeeping without changing the stepping mechanism. Build-23.log retains the diagnostic trace; the final code contains no trace.

S1 source total = 505 exact `FVA.Trust.codeLines`; declaration split = 222 S1-specific + 283 infrastructure (includes imports, namespace/options/attributes outside declarations). `Metrics.lean` regenerates `metrics-S1.tsv`; `declarations-S1.txt` = its role table. Declaration names omit the enclosing namespace: generic files = `FVA.Wasm.Exec.Ref`, arm files = `Subjects.Lz4C.SpikeD`. D1 conformance: structural/total definitions only; no partial/opaque/unsafe proof dependency added. LSP probe on Copy.lean: Lean language server unavailable; all checking uses the real Lean compiler.

S5 uses named code tails so the stepper sees the shortcut block while the decoder's unexecuted tails stay symbolic. The source buffers' separation proves that the literal copy preserves the offset bytes. S1 then composes the 16-byte literal call and the three match calls (8 + 8 + 2); `fwd_add` gives the frozen 18-byte ordered-copy post-state. Every branch reaches its exact `ShortExit`, with the original caller-local list retained.

S5's hard join = repeated local updates, not a new instruction semantics. Full-context sorting attempts were stopped by observed PID: build 68 (278.78 s, 2,888,984 KiB) and build 69 (453.03 s, 2,895,796 KiB), Lean rc 143 / runner rc 1. The final form uses two cached, generic-value list-update identities (`S5Locals.lean`, checked in 2.1 s), written with direct `List.set_comm` rewrites; the successful root build is 142 s. No claim that the stopped attempts would never finish. Composite read footprints also exposed `True ∧ …` residue: one shared tactic-body line now simplifies that residue after introducing the access bounds; the closing all-root recheck covers the change. The abandoned sort helper is removed.

For the next function: its agent supplies code slices, head-local facts and branch conditions per block; a decreasing counter, memory-composition identity and continuation per loop; an existing `CopyCall` theorem plus footprint inclusion and continuation per call. The next useful automation would capture the focus/unfocus adapters and the caller-local update identities, whose boilerplate remained explicit here. The engine boundary stays direct `Ref.seq` stepping; helper lemmas summarize proven runs, not an instruction-list evaluator.

## Closing verification + measurement scope

- All-root command (`build-73.log`): `lake build FVATest.Subjects.Lz4C.SpikeD.S1 FVATest.Subjects.Lz4C.SpikeD.S2 FVATest.Subjects.Lz4C.SpikeD.S3 FVATest.Subjects.Lz4C.SpikeD.S4 FVATest.Subjects.Lz4C.SpikeD.S5`, under the 12 GiB cap → rc 0, no warnings, every printed root has exactly `[propext, Classical.choice, Quot.sound]`; 180.89 s whole command, 2,739,556 KiB max RSS. S5 = 162 s in this concurrent recheck; its first successful isolated build = 142 s. These are authoring runs; M2/M3 remain MAIN's controlled measurements.
- Final committed-source footprint = 1,682 code lines. Stage cost sum = 1,683 (S5 changes one existing tactic-body line, already charged once in S1); S5 new source = 341 (287 specific + 54 infrastructure/administration), plus that 1 changed infrastructure line. No generated source. Declaration table = retained prover/library declarations; imports, options, namespaces and attributes outside declaration spans are charged to infrastructure. Pattern-specific support is conservatively statement-specific.
- Measurement-only scratch support = `build` (shell logger), `Metrics.lean` (`FVA.Trust.codeLines` driver), `metrics-S*.tsv`, `declarations-S*.txt`, `tool-counts.tsv`; excluded from the committed prover-source M1 cells. Raw attempts, including failed/killed builds, remain in `builds.tsv`, `build-starts.tsv`, `build-*.log`. Metrics regeneration: run `lake env lean --run <report-dir>/Metrics.lean <module-files…>` inside this worktree. Tool counts use this arm's `agent-aspike-d-cca29b1740841bc8.jsonl`, not the parent transcript.
- Protocol source check: 23 owned Lean files selected from the base diff (expected 23, rc 0); prohibited-token positive control = 1 / rc 0, source matches = 0 / rc 1. Closing axiom-log positive control = 5 standard-only root lines / rc 0; `sorryAx` matches = 0 / rc 1. `git diff --cached --check` → rc 0.
- Report validator: 149 retained source-declaration rows, expected 149 / rc 0; planted placeholder cell → 1 cell / rejection rc 1; final report → 0 placeholder cells / rc 0. Source-level declarations are counted once; Lean-generated recursors, projections and elaboration auxiliaries are not separate source rows.
- One fresh sol author context from c736868, no successor or nested agents, no other arm's work read. Public checkpoint-1 machinery = the supplied baseline. All 73 logged build invocations sum to 2,841.11 s wall time, waits included; exact CPU-vs-idle/provider compute split = not measured (logs hold elapsed/RSS, not that split). Measurement-only source footprint, outside committed M1: Lean driver 30 code lines, shell logger 16 nonblank lines.
- Not run here: independent checker export/replay, full repository gate, mutation suite, controlled timing repetitions. No claim of eligibility or method superiority before MAIN's checks.

## Statement issues (a frozen statement that looked false or ill-posed: what, where, evidence)
none

## Checkpoints

| stage | commit |
|---|---|
| S1 | `04f4baf` |
| S2 | `4c95f26` |
| S3 | `db39765` |
| S4 | `b9adaf6` |
| S5 | `43b3653` |

Round-1 branch `wt/spike-d`, source checkpoint `43b3653`; all five stages committed. No Intent, CLAUDE, agent-role or other notify-set file edited. The report and raw observations remain in the assigned scratch directory for MAIN's validator/harvest.

spike-d-DONE-1

## Round 2

Start = 2026-11-01T14:34:47+09:00; deadline = 2026-11-01T17:34:47+09:00; base = 1148d68 (`wt/spike-d`, MAIN's merge). M0 = contended wall time. Frozen Seg.lean SHA-256 = ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001 (command rc 0). `MainAccept.lean` belongs to MAIN and stays untouched.

| statement | status | theorem | start | first successful build | build iterations | tool-use events | SegC-specific code lines | new infrastructure code lines | axioms | failure class + last obligation |
|---|---|---|---|---|---|---|---|---|---|---|
| SegC | proved | `Subjects.Lz4C.SpikeD.segC` | 2026-11-01T14:34:47+09:00 | 2026-11-01T15:06:57+09:00 | 7 (74–80) | 46 | 257 | 30 | `[propext, Classical.choice, Quot.sound]` (`build-80.log`) | none |

### Round-2 reuse

M0 = **32m10s contended wall time**, waits included; tool-use events = 46 in the inclusive ISO-second window (`tool-counts-round2.tsv`, same arm-only transcript as round 1). First successful SegC module build = 8.1 s; full command = 9.17 s, max RSS = 2,798,848 KiB (`build-80.log`). Every build uses the required 12 GiB / zero-swap cap. Independent replay, controlled timing repetitions and the full repository gate are not run here.

Round-1 engine code is unchanged: `wasm_dstep` in `FVA/Proof/Lib/Direct.lean` computes each `Ref.seq` successor and its uniqueness/footprint, with existing `Context` + `Footprint` transports and `wasm_step` / `wasm_access` simp equations. No new tactic or instruction-list evaluator. SegC adds only a generic 32-bit complement bridge (`xor32_not`, 7 code lines) to that engine's arithmetic vocabulary; the other 23 infrastructure lines are file/import/option/namespace scaffolding. `maxRecDepth 2048` is local to the two larger proof modules; the first loop elaboration hit the default depth, then the capped build passed. No kernel-check bypass.

The match-length loop's **execution steps are discharged by D+**, in the new `cm_loop` proof: `wasm_dstep` runs the bound check, guest byte load, signed-overflow test, pointer/local updates and byte-255 branch. A fuel induction justifies repetition. Its numerical invariant is `lim < p + fuel` and `acc + 255·fuel + 15 < 2^31`; the frozen 2 MiB profile establishes it from the initial state. The bound exit and a non-255 byte are symbolic-byte branches. The invariant proves the signed-overflow and final complement-overflow guards false in this profile. `cm_tail` and `cm_error4` are new D+ execution/cutpoint adapters in this unit, not borrowed execution summaries. Neither checkpoint `ExtDirect.ext_l1`, the other arm, nor a generic external extension-loop execution lemma discharges the loop.

### D3: three-way new-code split

Directory = `FVATest/Subjects/Lz4C/SpikeD/`; counts use `FVA.Trust.codeLines`, comments/blank lines excluded. The split is orthogonal to the specific/infrastructure split above. Instruction slices, code identities, direct step calls, cached execution-adapter calls and concrete branch splits → execution glue. The fuel contract/induction and `extM`/bound equations → induction/model. Slot preservation, contexts, result/exit assembly and file scaffolding → cutpoint plumbing; in particular `CMInv` preserves cutpoint slots, while the numerical loop invariant is in the induction/model column. A mixed source line follows its primary role. `layers-SegC.tsv` maps every one of the 287 code lines to a category and source line; `classify-SegC.awk` regenerates it.

| file | (i) engine execution glue | (ii) generic induction + model arithmetic | (iii) cutpoint plumbing | total |
|---|---:|---:|---:|---:|
| `SegCBase.lean` | 35 | 0 | 61 | 96 |
| `SegCLoop.lean` | 17 | 29 | 46 | 92 |
| `SegC.lean` | 15 | 13 | 71 | 99 |
| **Total** | **67** | **42** | **178** | **287** |

Layer validator = `validate-SegC-layers.awk`: checks each file's exact code-line count, unique (file,line) keys and the category set. A planted `unclassified` line → 1 error / rc 1; final map → 0 errors / rc 0. M1 = 287 new source lines: 257 SegC-specific + 30 infrastructure, no generated source. `metrics-SegC.tsv` and the declaration table below retain the split.

### Named reused lemmas + sources

`reuse-SegC.tsv` is the complete name/source list of **all 876 reused project-level theorems** retained in the compiled `segC` dependency closure, including generated equation/auxiliary lemmas. `ReuseSegC.lean` regenerates it from the imported theorem; it traverses all 14,765 constant dependencies without a search cap. Lean-core/Mathlib lemmas are baseline and excluded from this project-level listing. Definitional/rfl simplifications may erase lemma references; their unchanged equation sets live in `FVA/Proof/Lib/{Walk,Footprint,Direct}.lean`. This is an inventory, not a replacement for `fva trust`'s origin checks.

Round-1 Direct lemmas retained by name, source `FVA/Proof/Lib/Direct.lean`: `FVA.Wasm.Exec.Ref.add32`, `bitvec32_zero`, `bitvec32_zero._simp_1`, `eq32`, `gt32`, `instrStep_load8`, `instrStep_load8._proof_1_1`, `le32`, `ne32`, `toNat32` (the shared prefix `FVA.Wasm.Exec.Ref` applies to each). The scalar/step/footprint/context machinery behind them is listed exhaustively in the TSV, with source files.

New-to-this-round main interfaces: `Subjects.Lz4C.ConstLocals.set` (`FVATest/Subjects/Lz4C/Loop.lean`); `Subjects.Lz4C.iltS_zero` and its dependency `Subjects.Lz4C.ofNat_toNat` (`FVATest/Subjects/Lz4C/ExtCommon.lean`); frozen `Subjects.Lz4C.extM` definitional equations (`Seg.lean`, with `extM.eq_2` materialized in `Loop.lean`). The TSV also names every generated auxiliary for these. `Cut/SegA.lean` was read but supplies no execution or model lemma to this proof. Positive-control `ConstLocals.set` = 1 row / rc 0; `ExtDirect|ExtRefine|SpikeC|SpikeV` in the reused theorem/source list = no match / rc 1. No outside-engine loop execution reused.

### Round-2 declarations

| file | declaration | kind | code lines |
|---|---|---|---:|
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmBound` | SegC-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmFirst` | SegC-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmLoop` | SegC-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmExt` | SegC-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmTail` | SegC-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmCode` | SegC-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmCode_eq` | SegC-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmAfter4` | SegC-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmCtx7` | SegC-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cmCtx3` | SegC-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `CMInv` | SegC-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `CMInv.update` | SegC-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `CMResult` | SegC-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `xor32_not` | infrastructure | 7 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cm_error4` | SegC-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCBase.lean` | `cm_tail` | SegC-specific | 20 |
| `FVATest/Subjects/Lz4C/SpikeD/SegCLoop.lean` | `cm_loop` | SegC-specific | 85 |
| `FVATest/Subjects/Lz4C/SpikeD/SegC.lean` | `cm_extend` | SegC-specific | 67 |
| `FVATest/Subjects/Lz4C/SpikeD/SegC.lean` | `segC` | SegC-specific | 24 |

### Round-2 statement issues

none

### Round-2 close

- Commit `d511763` (`spike-d: SegC proven`) on `wt/spike-d`; only the three new `SegC*.lean` prover files changed from merge base `1148d68`. Existing S1–S5 engine/proofs unchanged. MAIN-owned, untracked `MainAccept.lean` remains untouched; it is the only worktree-status entry.
- Frozen Seg.lean SHA-256 rechecked = `ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001`. Build 80 rc 0; standard-only axiom audit; no warnings. No source `sorry`, native proof bypass, new axiom, partial/opaque/unsafe definition: planted source-token control = 1 / rc 0, new prover-source matches = 0 / rc 1. Staged whitespace/diff check rc 0.
- Source-declaration inventory = 19 rows; layer map = 287 unique source-line rows; reuse inventory = 876 unique name/source pairs. Their structural validators pass; the layer validator rejects its planted bad class. Report placeholder validator = 0 cells / rc 0. Measurement-only extraction/classification scripts and raw data are in the assigned report directory, not in the prover M1.
- The loop's execution proof is `cm_loop` in `SegCLoop.lean`, newly built with D+'s `wasm_dstep` / `Ref.seq`; the generic fuel induction and model equations do not replace execution stepping. No outside-engine loop execution borrowed. New infrastructure = `xor32_not` plus file scaffolding; engine API unchanged.
- Independent export/replay, controlled M2 repetitions and full gate remain MAIN's work. No Intent, CLAUDE, role/instruction or other notify-set file edited. No nested agents; no other arm's code read.

spike-d-DONE-2

## Production — SegB, SegD

Archived — C chosen; SegB proved, SegD partial: prologue, byte-copy loop, pointer geometry and byte-tail/head adapters are built.
Next obligation at stop — far match-rest adapter (S1 + S4), then near-rest and root composition; D+ production is archived, not merged.

SegB start = 2026-11-01T18:12:57+09:00; source base = d511763 (`wt/spike-d`). Production work, not a comparison round. Frozen Seg.lean SHA-256 matches ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001. Both statements audited against the recorded `wat/lz4-c.wat` before implementation: SegB's nested room tests, return/error path, wildcopy + offset read; SegD's offset check, zero/byte/table prologue, far/near match copies and next-head/error branches. No statement mismatch found in this audit. `MainAccept*.lean` remains MAIN-owned and untouched.

| statement | status | theorem | start | first green | builds | tool-use events | specific code lines | generic code lines | axioms | statement issues / last obligation |
|---|---|---|---|---|---|---|---|---|---|---|
| SegB | proved | `Subjects.Lz4C.SpikeD.segB` | 2026-11-01T18:12:57+09:00 | 2026-11-01T18:43:55+09:00 | 5 (81–85; 4 to first green) | 25 | 223 | 34 | `[propext, Classical.choice, Quot.sound]` (`build-84.log`, warning-free `build-85.log`) | none |
| SegD | archived incomplete — C chosen | `Subjects.Lz4C.SpikeD.segD` not yet written | 2026-11-01T18:50:52+09:00 | none | 9 checkpoint builds (86–94) | 48 through 19:32:33 | 298 partial | 183 partial | four key helpers standard-only (`check-SegD-checkpoint.log`); no segD theorem | context limit; prologue/byte-loop helpers built, rest/root not implemented |

### Production statement issues

none

### SegB checkpoint

Commit `218428c`; `lake --wfail build FVATest.Subjects.Lz4C.SpikeD.SegB` passes with standard-only axiom audit. Reused S2 (`s2`) for the near-end `memmove`, S3 (`s3`) for literal wildcopy, `fwd_source_byte`/`read_two`/`and15` for the original offset and nibble, and unchanged direct stepping. Code inventory: `metrics-SegB.tsv`, `declarations-SegB.txt`; M0 tool events: `tool-counts-SegB.tsv`. Only four new `SegB*.lean` files committed; frozen/MAIN-owned files untouched. Initial audit of both production statements is included in the SegB interval.

spike-d-DONE-3

SegD production start = 2026-11-01T18:50:52+09:00; base = 218428c.

### SegD context checkpoint — incomplete

Committed partial source = `f6529b8` on `wt/spike-d` (parent `218428c`, the completed SegB checkpoint). Only MAIN-owned `MainAccept.lean` and `MainAcceptR2.lean` remain untracked. The continuation plan below is retained for reference; D+ production is archived and not continued. No theorem SegD is claimed.

Context hook at 757K/837K requested a handoff. SegD has no theorem/root module. The final DONE-4 marker records the archive stop, not a proved SegD. All retained helper modules pass the latest capped `lake --wfail build`: run 94 rc 0, no warnings, 54.96 s whole command, max RSS 2,786,732 KiB. `d_prologue`, `byte_loop`, `d_near_bytes`, `prologue_geometry` were imported and audited separately (`CheckSegDCheckpoint.lean`, rc 0): each depends only on `[propext, Classical.choice, Quot.sound]`. The partial source is 481 code lines (298 specific, 183 generic/scaffolding); `metrics-SegD-checkpoint.tsv` + `declarations-SegD-checkpoint.txt` retain the inventory. Tool events through 19:32:33 = 48. No frozen statement issue found; the stop is context, not a claim that SegD is blocked.

Retained pieces:
- `FVA/Proof/Lib/DirectPacked.lean`: proved packed/full i32 loads/stores at arbitrary memory offsets; Nat-address corollaries are the pre-order `wasm_direct` rules. A fully generic BitVec-address pre-rule did not infer the store-memory facts early enough; the normalized-address corollaries solve that without changing the semantics.
- `SpikeD/SegDCode.lean`: `d_entry` kernel-checks `body5.drop 5 = dCode`; named prologue/near/far slices and contexts; `DInv` preserves constant locals plus local 3 = cpy, 4 = j under updates of 2/15/17/18.
- `SpikeD/ByteLoop.lean`: `byte_loop` directly proves the single-byte load/store loop, arbitrary dl/sl/el/tail/context, exact `fwdCopy` + endpoints; positive remaining length, one byte per induction step.
- `SpikeD/SegDModel.lean`: `prologue_geometry` gives a Nat p with `(prologue mem o off).2 = ofNat p` and `dst ≤ p ≤ o` (all offsets, including tables/negative dec64 words); `d_far_model`, `d_near_model_yes`, `d_near_model_no` reduce the frozen `matchRest` model to the exact copy chains. `d_fwd_optional` handles zero byte-tail length. `plus8_nat` lives here, not in SegDHead.
- `SpikeD/SegDBytes.lean`: `d_copy4` directly steps the four inline byte copies at offsets 0–3, exact ascending `fwdCopy`; `inc32_le`, `dec64_lt` are table facts.
- `SpikeD/SegDPrologue.lean`: `d_prologue` is complete. It directly steps both paths, composes S1 for memcpy8 / memcpy4, preserves table bytes below 131072, and returns `DProExit`: exact prologue memory/pointer, DInv + locals 17=o /15=m, at `dCode.drop 11` in ctx5. Small-offset path includes zero store + 4 sequential bytes + table loads. Build 93 already passed this proof; latest run 94 passes it after the model additions.
- `SpikeD/SegDHead.lean`: `d_jump` returns to the next main head; `d_near_bytes` executes `(dNear.drop 9)` (the `18 ≥ cpy` check, else byte loop) to `DHead` with `fwdCopy mem q p (cpy − q)`. Inputs include DInv, locals 18=q/2=p, `dst ≤ p ≤ q`, q within destination, cpy fitting. `chunks_extra7` supplies the strict-positive wildcopy margin.

Historical handoff plan — superseded by the archive choice; reference only:
1. Implement the far match-rest adapter: from `dFar` in ctx5, memcpy8 to `o+8` from p, then m<13 → main head; else locals 2=p+8,17=o+16 and instantiate existing `s4` (`MatchWildS4`). Weaken footprints into `ReadSet`; use `d_far_model` to identify memory. DInv keeps locals 3=cpy and 4=j through these updates.
2. Implement the near match-rest adapter, then a combined rest theorem. In `dNear`, cpy>oend−5 → error with prologue memory and unchanged local4=j. Otherwise optional `dNearWild`: when `o+8 < oend−7`, instantiate existing `wild_loop` at dl15/sl17/el10, tail=[], inside `dWildCtx`. Strict-positive `chunks_extra7` proves copy end≤oend; p≤o makes reads fit too. After that loop, execute the remaining 9 steps of `dNearWild` (8 instructions + its block exit): local2 becomes **original p + (lim − (o+8))**, local18=lim. It intentionally ignores the wildcopy's updated local17. Invoke `d_near_bytes` from `dNear.drop 9`; identify memory with `d_near_model_yes` / `d_near_model_no`.
3. Write `SegD.lean` with `theorem segD : SegD`. First unsigned match-pointer test (4 instructions + branch if bad): `off<65536`, `dst≥131072`, `dst≤o` give no underflow, so test equals `o < dst+off`; bad → Err with original store. Good → execute 5 more instructions setting local3=cpy=o+m+4, call `d_prologue`, get p via `prologue_geometry` and rewrite the pointer to `vI p`, then invoke the rest theorem. Root success/error memories compose with `Ref.setMem_twice`; use `HeadLocals.of_const` and DInv for head fields. Root `cpy<2^32` follows o≤2MiB and m<2^31; valid writes require cpy+5≤oend.
4. Run required capped `lake --wfail build` + `#print axioms`; update this row with first-green time and final M1/tool counts. Keep MainAccept*.lean and all frozen files unchanged. A proved-root continuation would have required a proof commit. The archive stop ends this branch without a SegD proof.

Latest command for the built checkpoint: `systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 -p OOMPolicy=continue lake --wfail build FVATest.Subjects.Lz4C.SpikeD.SegDPrologue FVATest.Subjects.Lz4C.SpikeD.SegDHead`. Raw attempts 86–94 and helper audit are preserved. No further proof writing in this context.

Archive stop commit = `d599006` (`spike-d: SegD WIP (archived, C chosen)`); no builds after the stop instruction. All task-owned source was already committed in `f6529b8`, so the archive commit is an empty checkpoint. SegD remains unproved; this marker closes the archived production task.

spike-d-DONE-4
