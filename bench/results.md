# Benchmark v2 results

Rubric: `rubric.md` (fixed before any graded run, with its dated addenda). FVA was built with the subjects known: the U14 groundwork is listed below, and FVA's library is not frozen against the subjects.

## Pilot (2026-10-24; not graded)

One run per arm on T1 and T4 (the rubric's pilot), model `gpt-6.1-sol`, reasoning effort `high`, codex-cli 0.163.0, 4-hour cap, one pinned CPU per run, FVA = the U7–U11 build (`wt/u9` 170bec1).

| arm | task | wall (s) | input tokens | cached | output | reasoning | status |
|---|---|---:|---:|---:|---:|---:|---|
| bare | T1 lz4-wasm | 402 | 589,647 | 548,864 | 12,184 | 3,934 | completed |
| prompted | T1 lz4-wasm | 757 | 2,904,806 | 2,795,136 | 23,230 | 10,786 | completed |
| fva | T1 lz4-wasm | 1,956 | 8,298,863 | 8,091,264 | 38,134 | 19,380 | completed |
| bare | T4 edger-cpm | 686 | 1,833,839 | 1,752,960 | 19,555 | 8,130 | completed |
| prompted | T4 edger-cpm | 780 | 3,598,290 | 3,507,200 | 21,870 | 6,457 | completed |
| fva | T4 edger-cpm | 2,424 | 11,584,908 | 11,454,848 | 57,349 | 29,794 | completed |
| tool (Frama-C) | T4 edger-cpm | 352 | 894,862 | 841,344 | 13,020 | 3,945 | completed |

- Cap: no run reached 4 hours → slowest run × 1.5 = 2,424 s × 1.5 = 3,636 s → rounded up to 30 minutes = 90 minutes per graded run.
- What the runs reported (not graded): every arm reported both known defects of each task. The bare, prompted and tool arms connected their results to the binary by executing it (wasmtime, Node) next to Lean or Frama-C facts about byte lists, rationals or C models; the fva arms stated their counterexamples as claims about the lifted binary and `fva trust` passed them.
- Mechanism findings, each fixed before the graded runs:
  - Read-only Mathlib store: 7 `.hash` files had lost the leading zeros of digit-only hashes, so Lake rewrote them on replay and `import Mathlib` failed with `permission denied` (one event in the prompted T4 run). `bench/tasks/make-packages` zero-pads them to their `.trace` entries and verifies the store (an `import Mathlib` project builds against it).
  - Frama-C: rootless podman cannot start inside the Codex sandbox (`newuidmap: Could not set caps`). The tool arm's `frama-c` is `bench/tools/broker-client`; `bench/tools/tool-broker` runs the same container outside the sandbox (no network, only the task directory mounted read-write).
  - fva arm: the vendored FVA package had no kernel canaries (`scripts/fetch-canaries` needs the network), so the fva T1 run searched the host and copied canary files from this repository (9 log hits). `bench/tasks/prepare` now ships the fetched canaries without cached verdicts. The other six runs show no read of this repository.
  - Lake warned on every build that the manifest was out of date (its `packagesDir` named the store, the lakefile did not); the task lakefiles now name the store too, and the warning is gone.
- Network: no log shows a network access attempt (no name-resolution or connection failure).
