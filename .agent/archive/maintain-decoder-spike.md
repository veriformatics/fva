# MAINTAIN — fvapi readiness question + decoder feasibility spike U19 (closed partial → IMPLEMENT)

Request: is fvapi's PROTOTYPE state sufficient to continue work in fva? Answer (user-confirmed): yes — fvapi reads fva at a pinned commit, fva has no dependency on fvapi; the fva-side client waits for fvapi's IMPLEMENT (D58). The user then ruled the paused bench v2 direction: decoder spike, in this MAINTAIN session; IMPLEMENT, if needed, in a fresh one.

## Rows (this request)
- [x] b854177 deferred: D58 fvapi client row; D57 scoped to the bench runs (the EdgerCpm `Lifted.lean` is gitignored); archive VM-mitigation corrected (a VM shields the host from D12, not the verdict from D48/D49)
- [x] 71991fe direction ruling recorded; Intent names fvapi (`fva trust` = verdict)
- [x] c16894d U19 contract (consultant-1: 1 pass / 7 fix / 1 risk, all adopted; scientist-1: comparison protocol replaced; advisor) + seam (footprint vocabulary, checker, Footprint library, instance lemma, slices) + checkpoint 1 (both routes, both builds) + M4 + E1 (scientist-1 appraisal, bounded wording adopted) + gate wiring
- checkpoint 2 + proof scaling → IMPLEMENT (routed; contract inventory = starting plan)

## Outcome
- Footprint claim form (D52 vocabulary): `Reads`/`Writes`/`Within`/`Throughout` (reviewed spec), `CallWithin` (`CAbi`), verified checker, `MustW`/`Until` library + tactics; reviewer-1 audit 8/8 pass.
- Checkpoint 1: the lz4 C literal-length extension loop, all inputs, footprint + 3 exits, proven by direct stepping and by refinement, on `-O2` (shipped) and `-O1`; standard axioms; historical + final-state exports accepted by leanchecker + con-leche.
- E1: no route dominates (order/carryover confounded; M2/M3 without 2× separation) → direct stepping provisionally by policy. Machine-facing iteration/induction proofs hold most route-specific source lines (D 74.7 %/76.1 %, R 61.0 %/63.7 %).
- Checkpoint 2 gate unmet (I4–I9: memcpy/memmove contracts, loops with calls, data-segment tables, main-loop ↔ LZ4 format, R3 converse, speculative-access ranges).

Teammates: researcher-1..3 (prior art: loop methods + scale, Lean 4 practice, Wasm proofs/footprints/LZ4), consultant-1 (contract), scientist-1 (protocol design; results appraisal), reviewer-1 (E2 audit).
