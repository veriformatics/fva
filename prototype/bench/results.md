# Results: bare agent vs agent + FVA (rubric = `rubric.md`, n = 1 per cell)

Runs archived in `runs/<arm>-<task>/` (Lean sources, VERIFICATION.md, final message, usage).
Agent = `codex exec`, user-config model + effort, fresh context, `-s workspace-write`; all 6
concurrent. Judge for M3/M4/M6 = `reviewer-1` (`verdicts.md`), MAIN spot-checked J3, J8.

| metric | bare (isqrt / sat_add / avg_floor) | fva (isqrt / sat_add / avg_floor) |
|---|---|---|
| M1 proof validity | clean build rc 0, std axioms, kernel replay accepts — 3/3 | `fva trust` PASS — 3/3 |
| M2 artifact link | C model only (fidelity 0/2000 mismatches) / own wasm decoder + semantics + C model / own 6-instr wasm decoder + semantics | pinned binary via shared FVA semantics — 3/3 |
| M3 requirements | 5/5 faithful; avg R1, R2 refuted + reported | 5/5 faithful; avg R1, R2 refuted + reported |
| M4 planted bug | reported with counterexample | reported with counterexample |
| M5 review surface (Lean code lines) | ≈109–315 / 160–303 / 143–261 (lower = defs + statements, upper = all code); 2/3 add custom `elab` metaprograms | 13 / 19 / 53 (+ shared, reviewed-once semantics 129 + lifter 164) |
| M6 over-claim | none ×3 | none ×3 |
| M7 wall-clock s | 645 / 563 / 460 | 451 / 547 / 351 |
| M7 tokens in (uncached) / out | 72K/26K · 106K/24K · 84K/18K | 82K/18K · 139K/22K · 81K/14K |

Reading (per rubric): parity on M3, M4, M6, M1 → no moat on correctness or honesty at this
task size. FVA ahead on M5 (≈5–20× smaller per-project review surface) + M2 uniformity: bare
proofs rest on per-project, unvalidated semantics (1/3 never reached the binary; 2/3 wrote a
fresh wasm decoder + semantics, never differential-tested) and custom elaborators FVA's audit
would reject. Cost ≈ parity (fva 20 % less wall-clock, 24 % fewer output tokens, n = 1).

Design limits: tasks are tiny straight-line/loop integer functions inside FVA's semantics
subset; README names the wasm artifact (primes bare agents toward the binary); same model both
arms; n = 1; wall-clock under 6-way CPU contention.

Observed FVA defect: inside the agent sandbox, `fva trust` kernel replay fails (nested `bwrap`
cannot create a netlink socket); fva-avg_floor worked around it with
`lake check --inadvisably-no-sandbox`.
