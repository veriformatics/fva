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

