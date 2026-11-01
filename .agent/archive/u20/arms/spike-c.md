# spike-c — U20 arm c report

Result = **5/5 frozen roots proven**, standard axioms only. Final code = `ce5c7397787ab6bb09e5ccd42893886400dbec00`; independent-checker eligibility remains MAIN's measurement. Instruction/spec edits = none.

Arm start = 2026-11-01T10:50:43+09:00; deadline = 2026-11-01T18:50:43+09:00. Base = c736868; branch = wt/spike-c. Lean LSP unavailable; `lake build` supplies elaboration diagnostics.

## Per statement
| stmt | status (proved / not completed) | theorem name | start (ISO time) | end (ISO time) | build iterations / M0 tool calls | statement-specific code lines | infrastructure lines used (new / reused) | `#print axioms` | failure class if not completed + last failed obligation + command/rc |
|---|---|---|---|---|---|---|---|---|---|
| S1 MemcpyS1 | proved | Subjects.Lz4C.SpikeC.s1 | 2026-11-01T10:50:43+09:00 | 2026-11-01T11:24:29+09:00 | 26 builds (first green = 25; cleanup = 26); 126 M0 tools | 281 (Code 41 + CopyFacts 24 + S1 216; module shells included) | 230 / 0 | [propext, Classical.choice, Quot.sound] | none |
| S2 MemmoveS2 | proved | Subjects.Lz4C.SpikeC.s2 | 2026-11-01T11:26:52+09:00 | 2026-11-01T12:10:12+09:00 | 15 builds (027–041; first green = 040; 036–038 terminated diagnostics); 94 M0 tools | 616 (module shells included; forward summaries adapted from own S1) | 16 net new + 1 changed / 230 reused | [propext, Classical.choice, Quot.sound] | none |
| S3 LitWildS3 | proved | Subjects.Lz4C.SpikeC.s3 | 2026-11-01T12:13:49+09:00 | 2026-11-01T12:18:49+09:00 | 4 builds (042–045); 12 M0 tools | 110 (Wild 87 + S3 23; module shells included) | 3 (local_pair_reset) / 246 reused | [propext, Classical.choice, Quot.sound] | none |
| S4 MatchWildS4 | proved | Subjects.Lz4C.SpikeC.s4 | 2026-11-01T12:20:13+09:00 | 2026-11-01T12:21:10+09:00 | 1 build (046); 2 M0 tools | 26 (module shell included) | 0 / 249 reused; S3 wildcard summary reused unchanged | [propext, Classical.choice, Quot.sound] | none |
| S5 ShortcutS5 | proved | Subjects.Lz4C.SpikeC.s5 | 2026-11-01T12:21:38+09:00 | 2026-11-01T12:55:46+09:00 | 15 builds (047–061; first green = 060; 061 roots + axioms); 59 M0 tools | 349 (S5 211 + ShortCode 53 + ShortFacts 72 + closing acceptance 13) | 19 (BlockNumeric) / 249 reused | [propext, Classical.choice, Quot.sound] | none |

## Files and declarations
| file | declaration | kind (infrastructure / S1…S5-specific / generated) | code lines (comments + blank lines excluded) |
|---|---|---|---|
| `FVA/Proof/Lib/BlockAttr.lean` | `[block_simp] registration` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockAttr.lean` | `module shell (imports, namespace, attributes, options, prints)` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.base` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.label` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.frame` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.fill` | infrastructure | 6 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.seq` | infrastructure | 21 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.access_fill` | infrastructure | 11 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.BContext.within` | infrastructure | 9 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.blockEval` | infrastructure | 9 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.TraceOK` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockEval.lean` | `FVA.Wasm.Exec.Ref.blockEval_until` | infrastructure | 23 |
| `FVA/Proof/Lib/BlockEval.lean` | `wasm_eval (tactic elaborator; open/in wrapper included)` | infrastructure | 37 |
| `FVA/Proof/Lib/BlockEval.lean` | `wasm_trace (tactic macro)` | infrastructure | 2 |
| `FVA/Proof/Lib/BlockEval.lean` | `module shell (imports, namespace, attributes, options, prints)` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ofNat32_toNat` | infrastructure | 2 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ofNat32_eq_zero` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.add32` | infrastructure | 2 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.add32_neg` | infrastructure | 7 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ltU32` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ne32` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.eqz32` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.and32_low` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.and32_high` | infrastructure | 15 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.mem_read_one` | infrastructure | 2 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.byte32_toNat` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.write_size` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.setMem_get` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.setMem_setMem` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.setMem_self` | infrastructure | 5 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.setMem_funcs` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.eval_decide_true` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.eval_decide_false` | infrastructure | 1 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.add32_m1` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.add32_m4` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ofNat32_add_m1` | infrastructure | 6 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.instrAccess_storePacked` | infrastructure | 6 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.instrAccess_store` | infrastructure | 6 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.iadd_mask1` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.iadd_mask4` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.ofNat32_sub` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockFacts.lean` | `FVA.Wasm.Exec.Ref.base_sub` | infrastructure | 5 |
| `FVA/Proof/Lib/BlockFacts.lean` | `module shell (imports, namespace, attributes, options, prints)` | infrastructure | 11 |
| `FVA/Proof/Lib/BlockNumeric.lean` | `FVA.Wasm.Exec.Ref.eq32` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockNumeric.lean` | `FVA.Wasm.Exec.Ref.leU32` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockNumeric.lean` | `FVA.Wasm.Exec.Ref.shr32_four` | infrastructure | 3 |
| `FVA/Proof/Lib/BlockNumeric.lean` | `FVA.Wasm.Exec.Ref.and32_fifteen` | infrastructure | 4 |
| `FVA/Proof/Lib/BlockNumeric.lean` | `module shell (imports, namespace, attributes, options, prints)` | infrastructure | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `anonymous example : MemcpyS1` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `anonymous example : MemmoveS2` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `anonymous example : LitWildS3` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `anonymous example : MatchWildS4` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `anonymous example : ShortcutS5` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Acceptance.lean` | `module shell (imports, namespace, attributes, options, prints)` | S5-specific | 8 |
| `FVATest/Subjects/Lz4C/SpikeC/Backward2.lean` | `Subjects.Lz4C.SpikeC.mb1_until` | S2-specific | 42 |
| `FVATest/Subjects/Lz4C/SpikeC/Backward2.lean` | `Subjects.Lz4C.SpikeC.mb4_until` | S2-specific | 60 |
| `FVATest/Subjects/Lz4C/SpikeC/Backward2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/BackwardBody2.lean` | `Subjects.Lz4C.SpikeC.MvPost` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/BackwardBody2.lean` | `Subjects.Lz4C.SpikeC.mb_rest_until` | S2-specific | 43 |
| `FVATest/Subjects/Lz4C/SpikeC/BackwardBody2.lean` | `Subjects.Lz4C.SpikeC.mb_path_until` | S2-specific | 62 |
| `FVATest/Subjects/Lz4C/SpikeC/BackwardBody2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cp1` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cp4` | S1-specific | 15 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpBlock` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpOuter` | S1-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpBody` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpBody_eq` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpDefaults_eq` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `Subjects.Lz4C.SpikeC.cpLocals_eq` | S1-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code.lean` | `module shell (imports, namespace, attributes, options, prints)` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.permLocal` | S2-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.permInstr` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mp1` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mp4` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpBlock` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpTail` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpForward` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mb1` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mb4` | S2-specific | 16 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mbRem` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mbInner` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpOuter` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpBody` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpBody_eq` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `Subjects.Lz4C.SpikeC.mpLocals_eq` | S2-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Code2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeC/CopyFacts.lean` | `Subjects.Lz4C.SpikeC.fwdCopy_size` | S1-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/CopyFacts.lean` | `Subjects.Lz4C.SpikeC.fwdCopy_add` | S1-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/CopyFacts.lean` | `Subjects.Lz4C.SpikeC.fwdCopy_one` | S1-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/CopyFacts.lean` | `Subjects.Lz4C.SpikeC.four_writes` | S1-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/CopyFacts.lean` | `module shell (imports, namespace, attributes, options, prints)` | S1-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeC/Forward2.lean` | `Subjects.Lz4C.SpikeC.mp1_until` | S2-specific | 35 |
| `FVATest/Subjects/Lz4C/SpikeC/Forward2.lean` | `Subjects.Lz4C.SpikeC.mp4_until` | S2-specific | 56 |
| `FVATest/Subjects/Lz4C/SpikeC/Forward2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/ForwardBody2.lean` | `Subjects.Lz4C.SpikeC.mp_tail_until` | S2-specific | 19 |
| `FVATest/Subjects/Lz4C/SpikeC/ForwardBody2.lean` | `Subjects.Lz4C.SpikeC.mp_forward_until` | S2-specific | 78 |
| `FVATest/Subjects/Lz4C/SpikeC/ForwardBody2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.backCopy` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.backCopy_size` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.backCopy_add` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.write_byte_one` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.move_fwd_step` | S2-specific | 19 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.move_back_step` | S2-specific | 20 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.move_zero` | S2-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.fwdCopy_eq_move` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.backCopy_eq_move` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `Subjects.Lz4C.SpikeC.four_back_writes` | S2-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/MoveFacts.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.cp1_until` | S1-specific | 35 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.cp4_until` | S1-specific | 56 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.CpPost` | S1-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.cp_tail_until` | S1-specific | 19 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.cp_body_until` | S1-specific | 78 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `Subjects.Lz4C.SpikeC.s1` | S1-specific | 18 |
| `FVATest/Subjects/Lz4C/SpikeC/S1.lean` | `module shell (imports, namespace, attributes, options, prints)` | S1-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/S2.lean` | `Subjects.Lz4C.SpikeC.mp_body_until` | S2-specific | 21 |
| `FVATest/Subjects/Lz4C/SpikeC/S2.lean` | `Subjects.Lz4C.SpikeC.s2` | S2-specific | 18 |
| `FVATest/Subjects/Lz4C/SpikeC/S2.lean` | `module shell (imports, namespace, attributes, options, prints)` | S2-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/S3.lean` | `Subjects.Lz4C.SpikeC.lit_code` | S3-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/S3.lean` | `Subjects.Lz4C.SpikeC.lit_entry_code` | S3-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/S3.lean` | `Subjects.Lz4C.SpikeC.s3` | S3-specific | 13 |
| `FVATest/Subjects/Lz4C/SpikeC/S3.lean` | `module shell (imports, namespace, attributes, options, prints)` | S3-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/S4.lean` | `Subjects.Lz4C.SpikeC.match_code` | S4-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/S4.lean` | `Subjects.Lz4C.SpikeC.main_tail` | S4-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/S4.lean` | `Subjects.Lz4C.SpikeC.s4` | S4-specific | 17 |
| `FVATest/Subjects/Lz4C/SpikeC/S4.lean` | `module shell (imports, namespace, attributes, options, prints)` | S4-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/S5.lean` | `Subjects.Lz4C.SpikeC.s5` | S5-specific | 204 |
| `FVATest/Subjects/Lz4C/SpikeC/S5.lean` | `module shell (imports, namespace, attributes, options, prints)` | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.shortCode` | S5-specific | 26 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.shortRest5` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.shortRest6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.shortRest7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.shortRest8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_main_code` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_body5` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_body6` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_body7` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_body8` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_instr_step` | S5-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_toVal` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_unique` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_ne_br` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_ne_return` | S5-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `Subjects.Lz4C.SpikeC.short_access` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortCode.lean` | `module shell (imports, namespace, attributes, options, prints)` | S5-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.head_decompose` | S5-specific | 18 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.tokenLs` | S5-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.matchLs` | S5-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.shortCtx` | S5-specific | 2 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.fwdCopy_outside` | S5-specific | 7 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.copy_source_byte` | S5-specific | 4 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.read_two` | S5-specific | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `Subjects.Lz4C.SpikeC.short_copy` | S5-specific | 22 |
| `FVATest/Subjects/Lz4C/SpikeC/ShortFacts.lean` | `module shell (imports, namespace, attributes, options, prints)` | S5-specific | 6 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `Subjects.Lz4C.SpikeC.wcBody` | S3-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `Subjects.Lz4C.SpikeC.wcLoop` | S3-specific | 1 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `Subjects.Lz4C.SpikeC.local_pair_reset` | infrastructure | 3 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `Subjects.Lz4C.SpikeC.wc_until` | S3-specific | 70 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `Subjects.Lz4C.SpikeC.chunks_spec` | S3-specific | 5 |
| `FVATest/Subjects/Lz4C/SpikeC/Wild.lean` | `module shell (imports, namespace, attributes, options, prints)` | S3-specific | 6 |

Counts = `FVA.Trust.codeLines`, applied to parser-delimited command spans by `Decls.lean`; every module shell counted once. Table = explicit top-level declarations + constructors; local bindings count inside their enclosing declaration; compiler-generated auxiliaries are not handwritten source. No generated source. Final 21-file arm = **1,650 code lines**: 268 infrastructure + 1,382 stage-specific (closing acceptance allocated to S5). Checkpoint additions = S1 511; S2 632 net (+ one pre-existing line changed); S3 113; S4 26; S5 368. MAIN computes the protocol's new+changed/diff coordinates from commits, not these net totals.

Measurement-only declarations, excluded from arm M1: `Count.lean/main` = 4 declaration lines (+1 import); `Decls.lean/main` = 16 (+4 import/open lines). The parser loader uses `unsafe` only to enable Lean parser initializers in this external measurement script; no theorem imports it. Raw measurements = `declarations.tsv`; logs = `build-001.log` … `build-061.log`.

## Engine notes (what an agent proving the next function writes per block, per loop, per call; what was hard; what you would build next)
- Engine = fuel-bounded `blockEval` over `seqUnique` + `seq`; result = final configuration + every pre-step access. One `blockEval_until` proof transports `Until`; `BContext` preserves saved operand stacks around labels/frames. S1–S5 discharge stepping by evaluator rewrites, never direct small-step tactics. The evaluator handles structured labels, branches, loop unfolding and call entry; induction handles unbounded loops; S1 summarizes calls in S3–S5. Fallback = none.
- Next function, per block: name its code slice + cut point, give fuel, supply arithmetic/access facts, then `wasm_eval <fuel> [facts]`. Per loop: invariant, decreasing count, block summary + state/copy-composition identities. Per call: instantiate a previously proven contract, widen its footprint, compose by `Until.trans`. Exits = ordinary continuation predicates; a join needs no duplicated suffix proof.
- S1: 17-step byte tails + 39-step four-byte groups. Generic simplification alone left later write-conditioned loads unresolved; eight explicit byte-range facts made the four-byte block compute. This is a real per-block authoring cost.
- S2: forward proofs reuse this arm's S1 text under a local permutation (author-maintained source, all counted; no generated-source discount). Concrete `ofNat32(base + 4294967295/4294967292)` states hit kernel deep recursion in builds 032/034, including maxRecDepth 20000. Symbolic BitVec bases + modular-add equations made the loops build in 16 s (035); native BitVec subtraction in caller states removed the remaining blow-up. Final modules build at default recursion limits (041). An internal postcondition preserved too much: memmove overwrites local 1. It now hides locals 1–6, preserving local 0. Frozen S2 unchanged. Builds 036–038 were terminated diagnostics, not successful checks.
- S3/S4: unchanged `wc_until`, parameterized by local indices + terminal tail. Three-step evaluator prefix → S1 call → 11/12-step suffix → induction; a terminal label remains for the adapter. S4 changes indices/tail and adds one evaluator step into the main-loop head. `fwdCopy_add` joins successive 8-byte copies.
- S5: `HeadLocals` decomposes into an exact 19-slot list with five arbitrary initial slots. Evaluator cuts at the token branch, two room tests, the offset/match tests and call sites. `short_*` pre-rules compute the main-loop instruction while retaining `mainLoop` as its continuation name; these are evaluator computation equations, not `Step`/`Until` stepping fallbacks. Four S1 contracts produce the 16 + 8 + 8 + 2 bytes. `fwdCopy_outside` proves the literal copy leaves source/offset bytes unchanged; exact byte addresses and copy composition prove all five frozen `ShortExit` cases.
- Next engine improvement to evaluate, not implemented here: infer fuel up to a call/branch/join; canonicalize pointer subtraction + fixed local lists; discharge byte-range conditions uniformly. The current manual fuel/cut naming is small but visible scaffolding.
- D1: arm-defined executable dependencies are structural/fuel-based; source scan checks the prohibited forms. Tactic metaprograms are outside proof terms. The transitive trust scan remains unrun by this arm. No frozen file changed.

## Checks, checkpoints and measurement limits

- Passed: final `lake build FVATest.Subjects.Lz4C.SpikeC.Acceptance` (061, rc 0); five root-type examples against the frozen statements; all five `#print axioms` = `[propext, Classical.choice, Quot.sound]`; final diff whitespace check. The module runs use the prebuilt imports supplied to the arm, not a clean Mathlib rebuild.
- Source boundary scans: prohibited forms = zero matches (rc 1); direct-stepping fallback names in arm proof modules = zero matches (rc 1). Positive control: `wasm_eval` in S4 expected 1, observed 1 (rc 0). All 21 committed arm source files covered. Final base-to-HEAD diff whitespace check rc 0. A subsequently appearing untracked `SpikeC/MainAccept.lean` was not created by this arm; left untouched and excluded from M1 (inference: MAIN's measurement input).
- Frozen hashes, actual = contract: Copy `5caf05ac56598440e5b7ee1f58db72c03f41badb7a3ea6342713abb622d57461`; Short `fc29768f1e15cd5aa491ac07e6ba9cd41c2c963f26fb9f51397905e0bf09113e`.
- Checkpoints: S1 `46fe122`; S2 `730df89`; S3 `578985e`; S4 `11b97b1`; S5 `ce5c739`. No abandoned stage. Root modules = `FVATest.Subjects.Lz4C.SpikeC.S1` … `.S5`; cumulative roots/type checks = `.Acceptance`.
- M0 tool counts = unique assistant tool-use events inside each ISO interval, excluding a previous checkpoint commit that shares a rounded start second; raw events + exclusions = `tool-call-counts.json`. Endpoint times are shell observations at second resolution; S4's successful-build command also ran the line counter. Build counts include cleanup/acceptance after first green, while M0 ends at first green. M0 ≠ end-to-end delivery latency.
- Nominal M4: S4/S3 specific lines `26/110 = 0.236`; M0 `57/300 = 0.190`. S2/S1 specific lines `616/281 = 2.192`; M0 `2600/2026 = 1.283`. One author, one slice; no superiority/scaling inference.
- Report validator passed (rc 0): planted placeholder fires once; clean table has zero; 161 declaration/module rows sum to 1,650 code lines; M0 event counts match their saved JSON. Raw result = `validation.log`.
- Not run by this arm: full gate (forbidden by brief), `fva trust`, independent export/replay, interleaved fixed-CPU fresh-process M2/M3. MAIN owns those measurements; Lean proof completion alone does not establish checker eligibility or engine superiority.

## Statement issues (a frozen statement that looked false or ill-posed: what, where, evidence)
none

spike-c-DONE-1

## Round 2 — SegC

Result = **proved**, commit `13431b9f93a027d11d10d68295238025d1a1db2f`; base = `2588dcc`. Start = 2026-11-01T14:34:36+09:00; deadline = 2026-11-01T17:34:36+09:00. M0 = **contended wall time**, not isolated CPU time. Every build ran in the requested `MemoryMax=12G`, `MemorySwapMax=0`, `OOMPolicy=continue` scope.

| statement | status | theorem | start | first green | build iterations / M0 tools | infrastructure code lines (new / reused) | SegC-specific code lines | axioms | failure class / last obligation |
|---|---|---|---|---|---|---|---|---|---|
| SegC | proved | Subjects.Lz4C.SpikeC.segC | 2026-11-01T14:34:36+09:00 | 2026-11-01T14:57:22+09:00 | 8 module builds (first green 007, cleanup 008); 43 M0 tools | 9 new / 265 unchanged own infrastructure-module lines | 238 | [propext, Classical.choice, Quot.sound] | none |

M0 = 1,366 s (22 min 46 s); raw tool events = `round2-tool-calls.json` (43 unique events inside the ISO interval). Final module build `round2-build-008.log` rc 0; first green `round2-build-007.log` rc 0. Cleanup removes an unused code-slice lemma. Independent export/replay not run by this arm.

### Reuse and execution mechanism

- Unchanged own engine: `BlockAttr.lean` (2 lines), `BlockEval.lean` (129), `BlockFacts.lean` (115), `BlockNumeric.lean` (19) = 265 existing infrastructure-module lines. The actual directly referenced lemmas are listed below; the total counts imported module source, not only live declarations. No S1–S5 source changed. `blockEval`, `TraceOK`, `blockEval_until`, `BContext`, `wasm_eval` remain unchanged.
- New generic support = `c_xor` (8 lines: i32 xor-all-ones → bounded Nat complement) + one `block_simp` registration of Lean core's `not_true_eq_false`. No new evaluator or soundness theorem.
- **The match-length loop's execution is discharged by this arm's engine.** `c_loop` rewrites 13-step bound/error blocks and 24-step continuing/terminal iterations with `wasm_eval`. Ordinary induction follows `extM` fuel. Invariants = `lim ≤ q + fuel`, `acc + 255*fuel ≤ 255*n`; `n ≤ 2097152` then excludes signed overflow and the footer's `acc + 15 > ~o'` guard. No `ExtDirect.ext_l1`, generic external execution lemma, or direct-step tactic discharges the loop.
- `cOuter`/`cWrap` retain every dormant continuation, including the epilogue after block @2. `c_atX4`/`c_err` package the exact frozen cutpoints; the model proof does not replace that execution linkage.
- Default recursion depth 1000 failed during nested-label evaluator simplification (003). Depth 4000 let those finite rewrites finish; no proof-checking bypass. First 4000-depth build exposed a 255-vs-symbolic-byte state mismatch, repaired by specializing that branch before the induction call. Final build = 11 s on the contended host; not an M2 measurement.
- Frozen `Seg.lean` sha256 still `ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001`. MainAccept.lean left untouched. No instruction/spec edits.

### Three-way code split (D3)

All 247 new code lines counted once. Axes are separate: generic-vs-SegC-specific = **9 / 238**; execution/model/plumbing = **73 / 58 / 116**. Allocation is semantic, not a timing measurement. Mixed declarations are split by source blocks; exact nonblank/noncomment declaration-relative ranges = `round2-lines.json`. Headers and result assembly count as plumbing. Evaluator calls, footprint discharge and execution-summary composition count as execution glue. Invariants, case/induction control and `extM` equations count as model arithmetic. Module setup is allocated by purpose (recorded in the JSON), not dropped.

| declaration | code lines | infrastructure / SegC-specific | execution glue | model arithmetic | cutpoint plumbing |
|---|---|---|---|---|---|
| `cGuard` | 3 | 0 / 3 | 3 | 0 | 0 |
| `cFirst` | 3 | 0 / 3 | 3 | 0 | 0 |
| `cLoopBody` | 6 | 0 / 6 | 6 | 0 | 0 |
| `cLoop` | 1 | 0 / 1 | 1 | 0 | 0 |
| `cExt` | 1 | 0 / 1 | 1 | 0 | 0 |
| `cTail` | 3 | 0 / 3 | 3 | 0 | 0 |
| `cSegment` | 3 | 0 / 3 | 3 | 0 | 0 |
| `c_code` | 1 | 0 / 1 | 1 | 0 | 0 |
| `c_after3` | 2 | 0 / 2 | 2 | 0 | 0 |
| `cLocals` | 5 | 0 / 5 | 0 | 0 | 5 |
| `c_const` | 3 | 0 / 3 | 0 | 0 | 3 |
| `c_decompose` | 16 | 0 / 16 | 0 | 0 | 16 |
| `c_atX4` | 6 | 0 / 6 | 0 | 0 | 6 |
| `c_err` | 6 | 0 / 6 | 0 | 0 | 6 |
| `cOuter` | 4 | 0 / 4 | 0 | 0 | 4 |
| `cWrap` | 2 | 0 / 2 | 0 | 0 | 2 |
| `c_xor` | 8 | 8 / 0 | 0 | 8 | 0 |
| `c_footer` | 16 | 0 / 16 | 2 | 3 | 11 |
| `c_finish` | 11 | 0 / 11 | 2 | 0 | 9 |
| `cResult` | 5 | 0 / 5 | 0 | 3 | 2 |
| `c_loop` | 63 | 0 / 63 | 19 | 23 | 21 |
| `segC` | 67 | 0 / 67 | 22 | 20 | 25 |
| `module shell` | 12 | 1 / 11 | 5 | 1 | 6 |
| **total** | **247** | **9 / 238** | **73** | **58** | **116** |

### Reused lemma inventory (D3)

The table lists **all 47 direct reused project theorem constants** appearing in the new declarations' types/bodies, with their defining source. Names and modules come from Lean's environment, not a source-text guess. Full direct inventory, including core/Mathlib = **161 named theorems** in `round2-reused-all-lemmas.tsv`; project subset = `round2-reused-lemmas.tsv`. Compiler auxiliaries from SegC itself are new, not reused; transitive internals of these already-listed library lemmas are not expanded. Regenerate with `Round2Reuse.lean` (`--all` includes core/Mathlib). Numeric main lemmas used explicitly = `Subjects.Lz4C.igtU_ofNat`, `Subjects.Lz4C.iltS_zero` from `ExtCommon.lean`; no `Cut/SegA.lean` lemma is used.

| source | origin | every direct reused project lemma |
|---|---|---|
| `FVA/Proof/Lib/BlockEval.lean` | own S1–S5 infrastructure | `FVA.Wasm.Exec.Ref.blockEval_until` |
| `FVA/Proof/Lib/BlockFacts.lean` | own S1–S5 infrastructure | `FVA.Wasm.Exec.Ref.add32`, `FVA.Wasm.Exec.Ref.eval_decide_false`, `FVA.Wasm.Exec.Ref.eval_decide_true`, `FVA.Wasm.Exec.Ref.mem_read_one`, `FVA.Wasm.Exec.Ref.ne32`, `FVA.Wasm.Exec.Ref.ofNat32_toNat` |
| `FVA/Proof/Lib/BlockNumeric.lean` | own S1–S5 infrastructure | `FVA.Wasm.Exec.Ref.eq32`, `FVA.Wasm.Exec.Ref.leU32` |
| `FVA/Proof/Lib/Context.lean` | main baseline | `FVA.Wasm.Exec.Ref.Context.fill.eq_2` |
| `FVA/Proof/Lib/Footprint.lean` | main baseline | `FVA.Wasm.Exec.Ref.Until.mono`, `FVA.Wasm.Exec.Ref.atAccess_label`, `FVA.Wasm.Exec.Ref.atAccess_plain`, `FVA.Wasm.Exec.Ref.instrAccess_loadPacked`, `FVA.Wasm.Exec.Ref.seqAccess_cons_i32`, `FVA.Wasm.Exec.Ref.seqAccess_cons_none`, `FVA.Wasm.Exec.Ref.seqAccess_cons_val`, `FVA.Wasm.Exec.Ref.seqAccess_nil` |
| `FVA/Proof/Lib/Walk.lean` | main baseline | `FVA.Wasm.Exec.Ref.atInstr_br`, `FVA.Wasm.Exec.Ref.atInstr_instr`, `FVA.Wasm.Exec.Ref.atInstr_label`, `FVA.Wasm.Exec.Ref.atUnique_label`, `FVA.Wasm.Exec.Ref.atUnique_plain`, `FVA.Wasm.Exec.Ref.beq_decide'`, `FVA.Wasm.Exec.Ref.blt_decide`, `FVA.Wasm.Exec.Ref.isTrapOnly_nil`, `FVA.Wasm.Exec.Ref.seqUnique_cons_i32`, `FVA.Wasm.Exec.Ref.seqUnique_cons_none`, `FVA.Wasm.Exec.Ref.seqUnique_cons_val`, `FVA.Wasm.Exec.Ref.seqUnique_nil`, `FVA.Wasm.Exec.Ref.seq_cons_i32`, `FVA.Wasm.Exec.Ref.seq_cons_none`, `FVA.Wasm.Exec.Ref.seq_cons_val`, `FVA.Wasm.Exec.Ref.seq_nil`, `FVA.Wasm.Exec.Ref.toVal_block`, `FVA.Wasm.Exec.Ref.toVal_br`, `FVA.Wasm.Exec.Ref.toVal_brIf`, `FVA.Wasm.Exec.Ref.toVal_ibinop`, `FVA.Wasm.Exec.Ref.toVal_irelop`, `FVA.Wasm.Exec.Ref.toVal_label`, `FVA.Wasm.Exec.Ref.toVal_loadPacked`, `FVA.Wasm.Exec.Ref.toVal_localGet`, `FVA.Wasm.Exec.Ref.toVal_localSet`, `FVA.Wasm.Exec.Ref.toVal_localTee`, `FVA.Wasm.Exec.Ref.toVal_loop` |
| `FVATest/Subjects/Lz4C/ExtCommon.lean` | main baseline | `Subjects.Lz4C.igtU_ofNat`, `Subjects.Lz4C.iltS_zero` |

### Statement issues

none

### Validation and limits

- Final capped module build 008: rc 0, standard axiom closure. Full gate, independent replay/export and isolated M2 timings were not run by this arm.
- Source checks: positive control `wasm_eval` expected 11, observed 11 (rc 0); prohibited forms and outside-engine stepping names each zero matches (rc 1). Inherited engine diff = empty (rc 0); whitespace check rc 0; only new committed source = `SpikeC/SegC.lean`. Raw results = `round2-source-check.log`.
- Report validator passed: planted placeholder fires once, clean cells zero;23 declaration/module rows;247 code lines;73/58/116 three-way split;43 M0 events;47 project +161 total direct reused lemma entries. Raw result = `round2-validation.log`.
- External measurement helpers/data are excluded from proof-code M1. They inspect committed declarations; no theorem imports them. Statement domain = frozen SegC exactly; no sampled input or reduced claim.

spike-c-DONE-2

## Production — SegB, SegD

Base = `13431b9`; frozen Seg sha256 = `ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001`. Builds remain inside the requested 12G scope. MainAccept*.lean untouched.

| statement | status | theorem | start | first green | build iterations / M0 tools | new generic / specific code lines | axioms | failure class / last obligation |
|---|---|---|---|---|---|---|---|---|
| SegB | proved (`b2396f1`) | Subjects.Lz4C.SpikeC.segB | 2026-11-01T18:12:33+09:00 | 2026-11-01T18:38:21+09:00 | 3 capped builds; 17 M0 tools | 0 / 203 | [propext, Classical.choice, Quot.sound] | none |
| SegD | unknown | Subjects.Lz4C.SpikeC.segD | 2026-11-01T18:41:04+09:00 | unknown | unknown | unknown | unknown | unknown |

### Statement audit

SegB: room tests = `cpy > oend−12` or `q+len > iend−8`; near path checks exact input end + output capacity, calls func4, returns `cpy−dst`; other near paths jump to @2 with local4=q. Far path uses S3 and reads the original source's offset after the scratch copy. SegD: unsigned offset check precedes writes; prologue matches the ≥8 copy and all eight small-offset table profiles (negative dec64 entries included); capacity failure occurs after prologue; far/near copying and byte-loop exits match `matchRest`. The 2MiB premise prevents cpy wrapping; dst≥131072 + off<65536 prevents initial match-pointer underflow. This is a WAT/source audit; the exact slice equalities and theorem builds remain the acceptance checks.

### Statement issues

none

### SegB result

Commit `b2396f1a89c1b7c8dfab4f595dda68f2da44d654`; M0=1548 s contended (includes the upfront audit of both production statements). New `SegB.lean`=203 specific code lines, no engine changes. Reuses own `s2`, `s3`, `head_decompose`, `copy_source_byte`, `read_two`, SegC `cOuter`, unchanged evaluator + numeric facts; main `HeadLocals.of_const`, `off_lt`. Exact return crosses the function label/frame and restores the caller. Raw build logs=`prodB-build-001.log`…`003.log`; source counts=`prodB-declarations.tsv`; events=`prodB-tool-calls.json`.

spike-c-DONE-3
