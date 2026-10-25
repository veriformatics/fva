# Benchmark v2 rubric (fixed before any graded run)

Question (Decisions: Benchmark v2): on real shipped code, does an agent with FVA reach a verified result that a reader can trust with less review, less time and less cost than an agent without it, and does it reach results the others cannot? The three sentences the bench exists to test, each as a pre-registered hypothesis that may fail:

- S-bug: "a bare agent 'verified' X; FVA showed the shipped binary is wrong" (H1: on T1 + T4, a non-fva arm claims a verification that the binary contradicts, while the fva arm reports the defect with a machine-checked counterexample on the shipped artifact).
- S-read: "a ~25-line spec of Y a biologist can read, proven about the real binary" (H2: on T4, the fva arm's trusted surface is ≤ 40 code lines at `faithful` M3, and M9 rates it readable).
- S-link: "the Pachter lab's Lean theorem now applies to the code they ship" (H3: on T6, the fva arm proves a statement about the shipped runorm binary that instantiates the lab's theorem's hypotheses, with a stated floating-point tolerance).

FVA was built with these subjects known (U14 groundwork is disclosed in `results.md`); FVA's library is not frozen against them. Runs whose outcome refutes a hypothesis are reported as such.

## Tasks (`tasks/<id>/`: inputs exactly as the agent sees them; plain-language requirements only)

| id | subject (pinned in `subjects/manifest.json`) | artifact given | requirements (README prose) | known defect (never stated to agents) |
|----|--------------------------------------------|----------------|-----------------------------|---------------------------------------|
| T1 lz4-wasm | lz4-wasm LZ4 block codec, hand-written WAT + shipped `.wasm` (1,226 B) | `.wasm`, WAT source, official LZ4 block format text | encoder output decodes with the reference decoder and obeys the block format; decoder reproduces the original for every valid block, reads only its input | encoder breaks end-of-block condition 3 on ~5 % of blocks; decoder reads past the input on the empty block `00` |
| T2 lz4-c | lz4 v1.10.0 `LZ4_decompress_safe` (C, unmodified) + the committed wasm build | C source, build script, `.wasm` | never reads outside `src[0..srcSize)` nor writes outside `dst[0..dstCapacity)`; returns the decoded size for a valid block, a negative value otherwise | none known |
| T3 lz4-rust | lz4_flex 0.14.0 decompress (Rust, unmodified) + the committed wasm build | Rust crate, shim, `.wasm` | as T2 for `lz4_decompress` | none known |
| T4 edger-cpm | edgeR 4.99.10: C `calc_cpm_raw` in the shipped emscripten `edgeR.so` + R `filterByExpr` | `edgeR.so`, C + R source excerpts, documentation | `cpm = count / library size · 10⁶` per entry; `filterByExpr` keeps a gene iff at least `min.count` reads in enough samples, as documented | a median-library sample with exactly `min.count` reads fails the threshold in ~13 % of library sizes (C vs R rounding) |
| T5 tmm | TMM normalization factors: edgeR `calcNormFactors` (R) vs RNAnorm 2.2.0 (Python) | both sources, a fixed count matrix, both outputs | each factor = the TMM definition (trimmed weighted mean of log ratios, documented trims and weights); RNAnorm's claim "identical to edgeR to at least 10 decimal places" | 18/150 simulated datasets differ (A-value rounding moves tied genes across the 5 % trim) |
| T6 pflog | runorm PFlog (Rust) + the Pachter lab's Lean CLR uniqueness theorem (`Invariance` package) | runorm source + `.wasm`, the lab's Lean files | PFlog's output satisfies the theorem's hypotheses (rank monotone, additive, relabeling-equivariant, depth-shift invariant, calibrated) as far as floating point allows, with the tolerance stated | exact equivariance fails at the bit level (row-centering order) |

Each task directory: `README.md` (requirements R1…), the inputs above, `CHECK.md` (what the agent must deliver: `VERIFICATION.md` with what is proven, how it connects to the artifact, the exact check commands, what could not be proven, and any defect found with a reproducer).

## Arms (same model + effort + cap for every run of a task; fresh `codex exec` sessions outside this repo, `bench/harness/run-session`)

- bare: P-bare = "This directory contains software and a README that states its requirements. Formally verify the software against them: produce machine-checked proofs that the shipped artifact meets each requirement, or a demonstration that it does not. Lean 4.35 with Mathlib is installed. When you finish, write VERIFICATION.md as CHECK.md describes."
- prompted: P-bare + P-principles (v1.1 text: smallest review surface + its size; prove properties of the shipped artifact, no model rewrite; independent kernels + known-false-proof tests; one third-party check command).
- tool (T2: Frama-C 33.0 WP; T3, T6: Verus 0.2026.10.18; T4: Frama-C on the C core; T1, T5: no established tool → arm skipped): P-bare + "Use <tool> (installed at <path>; see its manual) for the proofs."
- fva: P-bare + "Use FVA, the verification tool in `fva/` (a copy of its Lean package; start with `fva/AGENT.md`)." The package = `git archive` (no history) of the bench tag restricted to an include list: `FVA/` minus every subject-named module, `Main.lean`, `FVA.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `scripts/fetch-tools`, `trust/canaries/`, `AGENT.md`, `README.md`, `LICENSE`; excluded: `FVATest/` (examples, cheats, certificates, mutation tool), `bench/`, `docs/`, `.agent/`, `.claude/`, `prototype/`, and every U14 subject specification or proof (LZ4, edgeR, TMM, PFlog) even where it lives in the repo. The export command, its file list and its sha256 go in `results.md` before the first fva run; an arm that finds a subject-specific spec or proof in its package invalidates the cell.

All arms: no network beyond what the harness allows (pilot checks it); Lean 4.35 + Mathlib v4.35.0 available offline: every task directory is a Lake project whose `.lake/packages` holds a read-only copy of the pinned Mathlib with its oleans (the mechanism the pilot must show working); `wasmtime`/`wasm-tools` on PATH; pinned CPUs (one run per CPU set); wall cap = pilot-derived (below). T6 ships MAIN's port of the lab's `Invariance` files to Lean 4.35 + Mathlib v4.35.0 (the original targets Lean v4.30.0-rc2), identical for every arm, the port's diff in the task.

## Metrics (scored by MAIN unless noted; per run)

- M1 Proof validity: every theorem VERIFICATION.md claims rechecked outside the agent's sandbox: clean build rc 0, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}, no `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/`extern`/`debug.skipKernelTC`, kernel replay (`leanexport` → `lake check --from-export` + con-leche); Frama-C/Verus runs re-executed with their own checker. Score = valid / claimed.
- M2 Artifact link: (a) the shipped binary's bytes, hash-pinned (T5: the exact bytes of the producers' outputs, certified per output); (b) a hand-written model of the code; (c) nothing executable. For (b) on a wasm artifact: model fidelity vs wasmtime on the pinned artifact, 2,000 cases; for (b) on T5: the model's factors vs both producers' outputs on the given matrix.
- M3 Requirement faithfulness (judge = a fresh `reviewer` per arm, given the README, the official LZ4 / edgeR / TMM documentation, the theorem statements + every definition they use, VERIFICATION.md): per requirement → `faithful` | `weaker` | `not proven, reported` | `missing` | `false claim`. MAIN rechecks every non-`faithful` verdict.
- M4 Defect outcome (T1, T4, T5, T6): `reported with a machine-checked counterexample on the artifact` | `reported with an executed reproducer` | `reported vaguely` | `spec silently weakened` | `false verification claim`.
- M5 Trusted surface (headline): code lines + definitions a reviewer must trust, at equal M3 — split into (i) the requirement statement, (ii) link + model (semantics, decoders, models the agent wrote), (iii) checker code the agent wrote; fva arm: `fva trust`'s review surface, with FVA's reviewed-once base counted apart.
- M6 Over-claim (same judge as M3): sentences in VERIFICATION.md asserting more than M1–M4 support.
- M7 Cost: wall-clock (graded runs only on an otherwise idle host: no proof builds, mutation runs or other benchmark-unrelated heavy jobs), input / cached / output / reasoning tokens (last completed `codex --json` snapshot), finished (VERIFICATION.md written before the cap).
- M8 Independence: MAIN injects C1 `sorry`, C2 `axiom False`, C3 kernel bypass, C4 one changed artifact byte into copies of the finished project, one at a time; caught = the run's own documented check exits nonzero or names the problem.
- M9 Readability proxy (judge = a fresh `reviewer`, domain-reader persona: a bioinformatician for T4–T6, a systems programmer for T1–T3): rates whether each requirement's statement can be read and checked against the README without reading proofs → `readable` | `readable with effort` | `not readable`, with the line count read.
- M10 Path found: did the run reach any machine-checked statement about the shipped artifact (M2 (a))? The "no path" cases of the Decisions are runs with M10 = no.

## Reading the result

Per task, median and spread over n runs per cell; no significance claims at n = 5. H1–H3 are read off M4/M10, M5+M3+M9, and T6's M1–M3 respectively. FVA wins a task when its M5 at equal M3 is smaller, or M4/M10 is better, without an M7 loss beyond 2×; parity is reported as parity; a loss as a loss.

## Protocol

- n = 5 per cell (user ruling); arms of one task interleaved, one run per pinned CPU set, the order randomized per task with a recorded seed.
- Pilot (before any graded run): one run per arm on T1 and T4 at a 4-hour cap; pilot runs are not graded; their logs show sandbox, network, Mathlib and tool behavior. Per-run cap: if any pilot run reached the 4-hour cap, the cap stays 4 hours; else the slowest pilot run (every arm counted) × 1.5, rounded up to 30 minutes.
- Before the graded runs, MAIN reports the pilot's per-run time + tokens and the projected total for every cell × n to the user, who decides the full set or a reduced task set (the subscription budget is the user's).
- Model + effort fixed for all arms (recorded in `results.md`); auth = the user's Codex login copied per run by the harness.
- MAIN does not touch a run while it runs; a crashed or capped run counts as finished = no and is scored on what it left. A run stopped by a model usage limit (rate-limit or quota events in its log) is discarded, never scored, and rerun once the limit resets.
- Deviation = a dated addendum here + a note in `results.md`, before the affected runs.

## Addendum 2026-10-24 (before the pilot)

- The sandbox does not hide the host filesystem, and arms are not told where this repository is. A run whose command log (`stdout.jsonl`) shows a read of this repository's path is invalid: discarded and rerun, never scored.
- Pilot runs use the task ids `<task>-pilot`; tools for the arms live in `~/.cache/fva-bench/bin` (copies of the pinned `wasmtime` + `wasm-tools`), Mathlib in `~/.cache/fva-bench/packages-v4.35.0` (read-only).
- Model `gpt-6.1-sol`, reasoning effort `high`, for every pilot and graded run.

## Addendum 2026-10-24 (after the pilot, before the graded runs)

- Pilot: 7 runs (T1 × bare/prompted/fva, T4 × bare/prompted/fva/tool), none capped → per-run cap = slowest run (fva T4, 2,424 s) × 1.5 = 3,636 s, rounded up to 90 minutes. Record: `results.md` (Pilot).
- User rulings: the full task set (T1–T6 + the added task below); graded runs task by task as separate batches, with the Codex quota read after each batch; timing in an idle window: no MAIN heavy job on the host, the user pauses other heavy jobs during a batch, and each run records its CPU time and load average (`result.json`: `cpu_user_s`, `cpu_sys_s`, `max_rss_kb`, `load1_start`, `load1_end`) beside its wall-clock (M7 unchanged).
- Mechanism changes from the pilot (before any graded run): the read-only Mathlib store is built and verified by `tasks/make-packages` (7 hash files zero-padded); the task lakefiles name the store (`packagesDir`), so Lake no longer reports the manifest as out of date; the tool arm's `frama-c` = `tools/broker-client`, which `tools/tool-broker` serves outside the Codex sandbox with the same container (rootless podman cannot start inside the sandbox); the fva arm's vendored package includes the fetched kernel canaries (offline sandbox; a pilot run that lacked them read this repository).
- T2/T3 requirement R3: the format text says "When a block does not respect these end conditions, a conformant decoder is allowed to reject the block as incorrect", so a decoder may also accept such a block; R3 requires that a non-negative result come from input that parses as LZ4 sequences, with the decoded content as output, and leaves blocks that break only the end conditions open. Checked on the artifacts: lz4 C rejects the block `316162610100506161616261` at capacity 13 and decodes it at capacity 64; lz4_flex decodes it at both.
- T5 inputs: matrix = simulated dataset 70 of the spike (454 genes × 7 samples, "low" scenario); outputs produced by edgeR 4.99.10 (`normLibSizes`) and RNAnorm 2.2.0; largest relative difference 9.4 × 10⁻³.
- T6 inputs: runorm `9429aa0` + `subjects/runorm-shim` (static input/output buffers, C-ABI `pflog`), built reproducibly by `subjects/build-runorm` (sha256 `ab1fc4ed…`); the lab's Lean files ported to Lean 4.35 + Mathlib v4.35.0 (`tasks/pflog/invariance-port.diff`: 4 lines removed); R1 = τ = 1/(4α) with α = runorm's documented OLS overdispersion computed exactly (an unconstrained τ would admit an all-zero output: consultant-8), every output within a stated ε of `Invariance.shiftedCLR τ`, R2 = within-cell order, R3 = gene relabeling within ε. Checked on the artifact: 150 of 200 random relabelings are not bit-exact (largest difference 1.8 × 10⁻¹⁵).
- Added task T7 `glm-iround` (post-pilot selection at the user's request, disclosed in `results.md`): GLM 1.0.3 `glm::iround<double>` (current release; MIT), built by `subjects/build-glm` (66-byte module, sha256 `eded7ae1…`: `f64.add 0.5` then `i32.trunc_sat_f64_s`); requirement R1 = for every finite x in [0, 2147483647], the nearest integer (either neighbor at an exact half); known defect = 0.49999999999999994 → 1 (nearest 0); selection evidence: missed by 10^6 uniform values, 10^6 uniform bit patterns and 1,107 boundary values, caught by one test at the value just below one half (`.scratch/research/researcher-8.md`); arms bare, prompted, fva (no established C++ verifier among the baselines → no tool arm); n = 5.
- Subject groundwork (U14) runs after the bench tag: the fva arm's package holds FVA as tagged, with no subject-specific specification or proof.

## Addendum 2026-10-24 (2) (before the graded runs)

- User ruling: T6 (pflog) and the S-link sentence are dropped: no T6 batch, H3 is not evaluated, and "two sentences" replaces "three sentences" wherever this rubric counts them. The graded set = T1, T4, T5, T2, T3, T7, in this order. T6's material (task README, the runorm build, the ported lab files) stays in the repository for the deferred showcase (spec D33).
- Each graded batch = `harness/run-batch TASK SEED ARM…` (the seed and the run order go into `results.md`); the Codex quota is read with `tools/codex-quota` after each batch.

## Addendum 2026-10-25 (before the graded T1 rerun)

- T1 is the task `lz4-wasm`: the hand-written WebAssembly LZ4 block codec of gorhill/lz4-wasm, fetched from that repository at `8995cdef` (`dist/lz4-block-codec.wasm`, sha256 `4bda6947…`, the same bytes as before); its README and requirements are unchanged. LZ4 is an academic example of a widely known algorithm.
- The fva arm uses FVA tag `bench-v2.1`: neutral names in the shipped files (the canary formerly named after an exploit is `prelude-15704/replaced-prelude`), `fva init` refuses a project named `fva`, and no input names this repository (Lake metadata of the prebuilt build and of the package store rewritten; `prepare` refuses inputs that name it). Model and effort stay `gpt-6.1-sol` / `high` (user ruling).
- The first T1 batch (`bench-v2`, 2026-10-24) is superseded, not graded: its fva inputs were a project named `fva`, which cannot build until renamed (all 5 fva runs hit it), two fva runs read this repository through paths in Lake metadata, and one run was stopped by the model provider's safety classifier.
- Safety-classifier stops (user ruling): a run that the provider's safety classifier stops (`error`/`turn.failed` naming the classifier) is discarded, counted per arm in `results.md`, and replaced by the next run index, until each cell holds 5 completed runs. T1 runs first; any change it forces carries to every later task before that task's batch.


## Addendum 2026-10-25 (2) (before the second graded T1 rerun)

- The second T1 batch (seed 2, harness at `ae2bd7f`, 2026-10-25) is superseded, not graded. Its run directories sat under the host user's home directory, and Codex's workspace-write sandbox limits writes alone, so agents could read outside their run: two prompted runs read the host user's global agent instructions (`AGENTS.md`, verification practice included) in a parent directory, and seven runs listed other runs' file names (a scan of every command and its output found no read of their contents). Three runs were safety-classifier stops (bare 1, fva 2).
- From this batch on, `bench/harness/run-session` starts every run in a bubblewrap jail. The run sees the system directories, its own run directory, the arm tools, the Mathlib package store and the `PATH` entries under the home directory. The rest of the home directory (this repository, other runs, instruction files), `/tmp`, the system journal and the host's processes stay hidden. `result.json` records the visible paths (`jail.visible`) and the harness commit (`harness_commit`); a graded run carries both, and its harness commit is clean (no `-dirty` suffix).
- T1 reruns in full with seed 3: every arm × runs 1–5, safety-classifier stops replaced by the next run index (addendum 2026-10-25). The superseded runs stay outside this repository.

## Addendum 2026-10-26 (before the T1 replacement runs)

- Provider capacity errors (`error`/`turn.failed` "Selected model is at capacity") are infrastructure failures, like the usage-limit stops the protocol already treats as invalid: the run is discarded, counted per arm in `results.md`, and replaced by the next run index (the safety-classifier rule of addendum 2026-10-25). The seed-3 T1 batch had two (fva 1, fva 2; 0 completed turns each).

## Addendum 2026-10-26 (2) (before the T5 batch; user ruling)

- T5 R1/R2 (each output is the documented TMM factor within a stated tolerance): the documentation (Robinson & Oshlack 2010, `calcNormFactors.Rd`, RNAnorm's `TMM` docstring) does not fix how tied genes are trimmed. On the T5 matrix each output reproduces its own float64 algorithm bit for bit, while exact-arithmetic TMM with average-rank ties differs from both by up to 1.96%. A claim is `faithful` when the arm states its tie policy and tolerance and the claim holds under them, whether it reproduces the float algorithm or uses exact ties; a claim false under its own stated policy is a `false claim`; an arm that reports the tie ambiguity has it noted under M4/M6. R3 (RNAnorm's factors equal edgeR's to 10 decimal places) is false on this matrix under either policy.
