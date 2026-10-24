# Review ledger (IMPLEMENT — link reach + bench v2)

Rows stay until ruled; the phase closes with no open row. Verdict source = the fixed check set of each review; teammate claims are leads, MAIN's ruling decides.

## U2 reviewed binary-format spec vs Wasm 2.0 (reviewer-1, check set R1–R10, target 6bbfb4a)

| row | check | verdict | ruling |
|---|---|---|---|
| R1 | §5 productions of P all transcribed | pass | accepted |
| R2 | LEB128 rules | pass | accepted |
| R3 | opcode tables, 181 pairs | pass | accepted; independently backed by T5 (`numOp_table` … = kernel `rfl`) and E2 (`wasm-tools print` differential re-encodes from the spec tables) |
| R4 | immediates and operand orders | pass | accepted |
| R5 | module/section structure | pass | accepted |
| R6 | element (8) and data (3) segment encodings | pass | accepted |
| R7 | names (UTF-8) | pass | accepted |
| R8 | abstract syntax faithful to §2 (note N8: locals kept as encoded runs; carriers wider than the grammar, bounds restored by the binary relations) | pass | accepted: runs = consultant-2 ruling D6 (expansion belongs to U4); no extra accepted bytes |
| R9 | over-/under-acceptance | pass | accepted (static review; T1/T2 bind the decoder to the transcription, not the transcription to the spec) |
| R10 | profile exclusions (note N10: memory count / data memidx left to validation) | pass | accepted: validation = U6 by contract (C3/D2 ruling) |

## U3 reviewed numerics spec vs Wasm 2.0 §2.2.3 + §4.3 (reviewer-2, check set F1–F24 I1–I8 X1–X2, target 4c74e9a)

| row | check | verdict | ruling |
|---|---|---|---|
| F1–F4 | float syntax/WF/toReal; fbits/ofBits; rounding (`Ieee` via candidate pairs, even, rectify); `nans` | pass | accepted; independently backed by prover-6 adequacy (`ofBits_fbits`, `fbits_ofBits`, `ieee_total`, `ieee_functional`, `nans_nonempty`) |
| F5–F19 | each float operator's case chain (fmul zero-sign ruling, fge equation ruling checked against the test bytes) | pass | accepted; backed by the official scripts (E1: every float assertion passes through the impl, impl ∈ spec proven) |
| F20–F24 | trunc/trunc_sat/promote/demote/convert (D2, D3) + `onBits` lifting | pass | accepted |
| I1–I8 | integer auxiliaries + every integer op, traps, shifts mod N, extends | pass | accepted; backed by E1 (i32/i64/int_exprs assertions) |
| X1 | coverage: every non-SIMD numeric op + conversion defined | pass | accepted |
| X2 | no Lean-core edge semantics leak into a spec definition | pass | accepted |
| R1 (register) | contract N1 wording forbade all core `BitVec` ops in the spec; the spec uses `BitVec.ofNat/ofInt` + pointwise `&&&`/`|||`/`^^^`, faithful to the text | note | accepted: contract N1 narrowed (arithmetic/shift/division shortcuts stay proof-only; representation constructors + pointwise bitwise ops allowed) |

## U4 reviewed execution spec vs Wasm 2.0 §4.2/§4.4/§4.5.5 (reviewer-3, check set E1–E20 X1–X3, target 17c93e7)

| row | check | verdict | ruling |
|---|---|---|---|
| E1–E6 | values/defaults; store + instances + frames; extensional memory (read/write/grow); growtable; administrative instructions + values as constants; block contexts | pass | accepted |
| E8–E19 | numeric dispatch; reference, parametric, variable, table, load/store, bulk memory, control, br/return, call/call_indirect, invoke + frame exit, host invocation | pass | accepted |
| E7, X2, X3 | context rules, spurious/missing steps, nondeterminism: one-step collapse of a nested context around `trap` missing (F2, minor: two-step reachability agreed) | finding F2 | accepted → fixed: `EvalCtx` + `Step.trap` for every context with `E[trap] ≠ [trap]`; re-review check: `[label₀{} (label₀{} trap)] ↪ [trap]` derives in one step |
| E20 | claims: `Call*` lacked §4.5.5 invocation checks (extra or mistyped arguments still invoked) (F1, major) | finding F1 | accepted → fixed: `Val.HasType` + `InvokeOK` (address exists, arguments match parameter types in number and type) required by `CallMust`/`CallMay`; re-review checks: both counterexamples (nullary called with `[i32 7]`, `[i32]` called with `[f64 0]`) now refuted |
| X1 | coverage of every P instruction | pass | accepted |
| R1 (register) | §4.4.7 bulk-op prose asserts `d+1 < 2^32` after the range check; false at 65536 pages | note | accepted: the transcription wraps only the next zero-count iteration's pointer; every access stays exact; no change |
| R2 (register) | validity (`ValidHost`, store typing) not yet stated | note | accepted: contract S4/S5 + U6 interface (slices 2–3) |

## U4 re-audit: Instantiate.lean + Host.lean + F1/F2 fixes (reviewer-4, check set I1–I7 X1, target af3ca99)

| row | check | verdict | ruling |
|---|---|---|---|
| I1–I4 | allocModule (§4.5.3.10); import matching (§4.5.2); runelem/rundata/initCode order (§4.5.4); Instantiated incl. the initializer fixpoint device | pass | accepted |
| I5 | store extension per instance kind (appendix); HostOutcome.Allowed + ValidHost (§4.4.10) | pass | accepted, with register R1 |
| I6–I7 | F1 fix (Val.HasType, InvokeOK, Call*); F2 fix (EvalCtx + Step.trap) | pass | accepted: both fixes confirmed by a second reviewer |
| X1 | contradictions / missing requirements (validity excluded) | pass | accepted |
| R1 (register) | host outcome stores are not required to be valid (a mutable i32 global may hold an f64 in an allowed trapped store; exec-instructions.rst host requirement) | note | accepted: store validity = the deferred U6 store typing (U4 R2); `ValidHost` gains the valid-store condition when U6 defines store typing |
| R2 (register) | upstream: §4.5.4 prose runs all active segments before declarative drops; the equations interleave by segment index | note | accepted: the transcription follows the equations (FVA's convention) |
| R3 (register) | upstream: appendix extension keeps the table/memory type unchanged while growth updates its min | note | accepted: growth-compatible reading (same element type/maximum, size non-decreasing) |

## U4 LoaderReady / RunsExport (b119c25) — open for the U4/phase closing review

| row | check | verdict | ruling |
|---|---|---|---|
| L1 | `LoaderReady` = Instantiated, then exported `__wasm_apply_data_relocs`, then `__wasm_call_ctors`, before any other export (tool-conventions DynamicLinking.md, pinned 25aceba: "the loader will call it after the module is instantiated, and before any other function, including `__wasm_call_ctors`"); an absent export leaves the store unchanged | open | MAIN self-check matches the quoted protocol; adjudication by the closing reviewer |


## U12 fvamut runner (reviewer-5, check set R1–R9, targets wip/u12 9d10d0a → f30c52c → 68de45d)

| row | check | verdict | ruling |
|---|---|---|---|
| R1 | kill witnesses only (K4 rc protocol) | finding R1a (test-spec mapped its own timeout/spawn failure to rc 1) | accepted → fixed: rc 124/signal → crash marker (exit 3), 126/127 → infra (exit 2); re-check: stubbed statuses 0/3/2 |
| R2 | error-line mapping (multi-edit GIB, multi-line GME, later declarations) | pass | accepted |
| R3 | digests cover every outcome input; reuse + cache conflict | finding R3a (test argv joined by spaces: `'a b'` ≡ `a b`) | accepted → fixed: argv serialized as JSON in the stage line; re-check: exactly 2 rows stale, fresh shows 2 survivors |
| R4 | worker isolation + restoration | finding R4a (`cp -p` into `.lake/build` kept an old mtime: leak to the next mutant) | accepted → fixed: build reset by ctime (`find -cnewer`); battery case `leak` seen red on the old reset (leakB killed), green now |
| R5 | mode semantics, current/complete rows | finding R5a (ad-hoc `check` green with no executions) | accepted → fixed: an ad-hoc selection needs a current row per selected mutant |
| R6 | rulings binding, staleness, vocabulary | finding R6a (duplicate ruling id hid a stale line) | accepted → fixed: duplicate ids rejected (battery case) |
| R7 | site exclusions + operator coverage | finding R7a (`show T from e` dropped `e`) | accepted → fixed: the `from` part is walked |
| R8 | battery labels vs assertions; E1 completeness | finding R8a (dependency cases checked stale counts only; then `ran()` discarded the rerun rc) | accepted → fixed: each case reruns `update` and asserts the exact executed ids + rc (`reran`), plus `order-free`, `leak`, `shared` cases; re-check: the reviewer's poisoned-rc reproducer now fails the battery (rc 1), the battery is green |
| R9 | processes, setup, incomplete runs | finding R9a (`--workers 0` green with nothing run) | accepted → fixed: zero workers = usage error; a run leaving a selected mutant without a result is a finding |
| X1 (register) | contract G1 said `check` never writes, yet it writes its local cache | note | accepted: G1 = writes no tracked file |

## U12 mutation survivors (reviewer-8, check set = U2/U3/U4 contracts + U12 L1–L3, targets 877d19b = wip/u12 + the B5 rows)

| row | check | verdict | ruling |
|---|---|---|---|
| F1 | decoder error coordinates (U2 I1 "failures carry bytes-left, rebased at each sub-input, file offset = `len − rem`") — 33 survivors (`Reader.byte/uleb/sleb/sub/utf8`, `Module.decode`, `Instr.seq`) | specified | accepted → killed by `FVA/Proof/Pin/Decode.lean` (15 `rfl` pins on concrete failures) |
| F2 | `Impl.nanOf` default sign (U3 I2) | specified | accepted → killed by `nanOf_default` |
| F3 | imported table addresses precede defined ones (U4 S5, Wasm 2.0 §4.5.3) | specified (major: no test covered it) | accepted → killed by `allocModule_tables_imports_first` |
| F4 | element initialization before data (U4 S5) | specified | accepted → killed by `initCode_elems_first` |
| F5 | reference-local default is null (U4) | specified | accepted → killed by `default_ref` |
| F6 | memory growth to exactly 2^16 pages succeeds (Wasm 2.0 `growmem`) | specified | accepted → killed by `grow_to_limit` |
| F7 | `ref.is_null` on null returns true (Wasm 2.0 §4.4.2) | specified | accepted → killed by `isNull_null` |
| F8 | `TableInst.grow` bound + max (5 inconclusive rows, test:spec crashed under the memory cap) + `ictz` of 1 | specified | accepted → killed by `tableGrow_limit`, `ictz_one` |
| E | the 66 remaining survivors: 15 equivalent (no input distinguishes, argument per row), 51 unspecified (contract clause per row, `path@sha16`) | ruled | accepted: independent ruler (reviewer-8 ≠ the author of the tests and proofs involved); MAIN rematched every unspecified anchor (6/6 clause texts `rg -Fc` = 1); rulings in `FVATest/Mutate/rulings.tsv` |
