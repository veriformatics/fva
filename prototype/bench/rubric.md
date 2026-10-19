# Benchmark: bare agent vs agent + FVA

Question: does FVA beat "point an agent at the repo and ask it to formally verify it"?
Rubric fixed before any run; scoring follows it as written.

## Design

- Tasks = `tasks/{isqrt,sat_add,avg_floor}`: C source + README requirements (R1…) + build
  command + pinned `.wasm`. `avg_floor` carries a planted bug: `(a + b) >> 1` wraps, so R1/R2
  fail for 2797/20000 sampled inputs (e.g. `avg_floor(INT_MAX, INT_MAX) = -1`). Agents are not
  told about any bug.
- Arms, same agent (`codex exec`, user-config model + effort, `-s workspace-write`, fresh
  context, no project instructions):
  - bare: task copied to an isolated dir outside the FVA repo (`/tmp/fva-bench/bare-<task>`,
    own git repo). Prompt P-bare.
  - fva: task copied to `prototype/fva/examples/<task>` of a fresh worktree of this repo.
    Prompt P-fva = P-bare + FVA pointer.
- Both arms: Lean 4.35 + lake installed, no Mathlib, no network. Both arms of a task run
  concurrently (equal CPU contention).
- n = 1 per cell → results are qualitative evidence, not statistics.

P-bare: "This repository contains C code and a README that states its requirements. Formally
verify this code: produce machine-checked Lean 4 proofs that the code meets its requirements.
Lean 4.35 and lake are installed; Mathlib is not available and there is no network. When you
are done, write VERIFICATION.md: what is proven, how the proofs connect to the code, the exact
commands that check the proofs, and anything you could not prove."

P-fva addition: "Use FVA (Formally Verify Anything), the tool in this repository: read
prototype/fva/README.md. Your task is in prototype/fva/examples/<task>; put your Lean project
there."

## Metrics (scored by MAIN unless noted)

- M1 Proof validity: each theorem VERIFICATION.md claims → clean `lake build` rc 0; `#print
  axioms` ⊆ {propext, Classical.choice, Quot.sound}; sources free of `sorry`, `admit`,
  `axiom`, `native_decide`, `implemented_by`, `extern`, `debug.skipKernelTC`; kernel replay
  (`leanexport` → `lake check --from-export`). fva arm: `fva trust` covers these. Score =
  valid / claimed.
- M2 Artifact link: theorems are about (a) the compiled binary bytes, hash-pinned, (b) a
  hand-written Lean model of the C, (c) nothing executable. For (b): model fidelity = the
  model evaluated by Lean vs wasmtime on the pinned `.wasm`, 2000 cases (edges + random) →
  mismatch count; note whether it models 32-bit wraparound.
- M3 Requirement verdicts (judge = `reviewer` teammate, given README requirements + theorem
  statements + the definitions they use + VERIFICATION.md): per Rk → `faithful` | `weaker` |
  `not proven, reported` | `missing` | `false claim`. MAIN spot-checks every non-`faithful`.
- M4 Planted bug (`avg_floor`): `reported with counterexample` | `reported vaguely` |
  `spec silently weakened` | `false verification claim`.
- M5 Human review surface: non-comment Lean lines a reader must trust = claim statements +
  every non-core definition they use (for (b): the model) + any trusted glue. fva arm:
  `fva trust` review surface; FVA's shared semantics + lifter counted separately as
  reviewed-once.
- M6 Over-claim (judge = reviewer): sentences in VERIFICATION.md asserting more than M1–M4
  support.
- M7 Cost: tokens (input / cached / output, codex `--json` usage), wall-clock, finished
  (agent ended its turn with VERIFICATION.md).

## Reading the result

Moat evidence = fva arm better on M2, M4 or M6 without a large loss on M7. Parity on M2–M6
= no moat from this prototype. Bare better = FVA adds cost without assurance.
