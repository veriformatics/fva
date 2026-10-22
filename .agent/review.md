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

