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
