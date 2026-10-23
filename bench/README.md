# Benchmark v2 preparation

Scope = acquisition, reproducible subjects, baseline smokes, session capture. MAIN owns the committed rubric, pilot, arm prompts, real launches, grading, results. No benchmark findings here. `check-prep` launches a mock Codex only.

## Commands

Repo root; Linux x86-64, Bash, curl, jq, tar, unzip, rsync, Podman, taskset, timeout:

```sh
scripts/fetch-tools
export PATH="$PWD/.tools/bin:$PATH"
scripts/fetch-bench-tools all
scripts/fetch-bench
bench/tests/smoke-tools
bench/tests/check-prep
bench/tests/check-build
bench/subjects/build-lz4
```

`fetch-bench-tools` accepts `rust`, `verus`, `frama-c`, `wasi-sdk`, `all`. Cached payloads are hash-checked every fetch; a mismatch fails. Downloads = `.cache/bench/downloads/<id>/`; tools + Rust homes = `.tools/`. Third-party archives/binaries stay untracked.

### Tool pins

Exact asset URLs + SHA256/image digests = `scripts/fetch-bench-tools`.

| tool | version |
|---|---|
| Verus | `0.2026.10.18.7d82994` |
| Rust | `1.99.1`; rustc-dev, llvm-tools, rustfmt, wasm32-unknown-unknown; project-local Rustup 1.29.2 |
| Frama-C evaluator | `33.0 (Arsenic)` official Linux bundle |
| Frama-C dependency image | `docker.io/framac/frama-c@sha256:4f0b7a2bd600c4daabfdcdfa393a3c18301e0db18f3b2739f1d9650193462d36` (tag 32.1) |
| C compiler | WASI SDK 34.0, clang 23.1.0-wasi-sdk |
| wasm tools/engine | existing `scripts/fetch-tools`: wasm-tools 1.262.0, Wasmtime 50.0.0 |

Frama-C 33.0 has no Docker Hub tag. The pinned 32.1 image supplies GCC/Why3/solvers; the wrapper explicitly runs the separately pinned 33.0 bundle at `/opt/fva-frama/bin/frama-c`, with its own `OCAMLPATH`. The 32.1 evaluator is not the baseline. Container = no network, bundle read-only, one writable workdir, keep-id UID mapping. Filenames after WORKDIR are workdir-relative.

```sh
bench/tools/verus bench/tests/fixtures/true.rs
bench/tools/frama-c --check-wp .cache/bench/task -wp-rte -wp-prover qed proof.c
```

Raw Frama-C rc 0 = analysis completed, including unproved goals. `--check-wp` owns a WP JSON report; rc 0 requires nonempty ordinary goals, all valid/passed. It rejects smoke-test verdicts. This is a convenience check, not a completeness/soundness claim about arbitrary Frama-C invocations. Smokes use Qed; external SMT provers remain a pilot check.

Subject metadata = `subjects/manifest.json`, six entries: lz4 v1.10.0 archive, lz4_flex 0.14.0 crate, lz4-wasm codec at 8995cdef, edgeR 4.99.10 emscripten archive + library, RNAnorm 2.2.0 sdist. edgeR archive/member hashes are checked independently. Licenses: lz4 lib BSD-2-Clause (whole archive also GPL-2.0-or-later); lz4_flex MIT; isolated codec BSD-2-Clause (byte-identical to gorhill/lz4-wasm, not the enclosing lz4-wasm project's license); edgeR GPL-2.0-or-later; RNAnorm Apache-2.0.

## Standalone wasm

`subjects/build-lz4 [OUTPUT_DIR]` defaults to `.cache/bench/wasm/`. `subjects/wasm/` = the pinned outputs, committed with `NOTICE` (lz4 BSD-2-Clause, lz4_flex MIT, Rust core MIT/Apache-2.0), so the gate's difftest runs without the build toolchains. Each call extracts fresh pinned sources and uses a fresh Cargo target dir. `subjects/lz4.sha256` pins outputs; `tests/check-build` builds twice, compares bytes, checks pins, drives exports in Wasmtime.

- C = unmodified `lib/lz4.c`, `LZ4_FREESTANDING=1`, authored `c-memory.c` memcpy/memmove/memset, clang wasm32 target, `-O2`, no libc/WASI.
- Rust = unmodified crate, no_std, defaults off; safe-encode/safe-decode/checked-decode on; no allocation. Minimal C-ABI shim; pinned rust-toolchain.toml + Cargo.lock; `--release --frozen`, opt-level 2, LTO, one codegen unit, panic abort.
- Both = fixed 2 MiB memory, 64 KiB stack, stripped metadata, zero imports. Target = Wasm 2 without SIMD; validation = `wasm-tools validate --features=wasm2,-simd`. Generic compiler target, SIMD/relaxed-SIMD disabled; bulk memory allowed, no unstable LLVM flag.
- Exports: C `LZ4_compress_default`, `LZ4_decompress_safe`; Rust `lz4_compress`, `lz4_decompress`; both `(src, dst, input_length, output_capacity) -> i32`; exported memory. Caller supplies live, non-overlapping buffers; Rust pointers nonnull even for empty slices; lengths fit signed 32-bit bounds. Return = bytes written; C compression failure 0, Rust compression failure −1; decompression failure negative.
- Smokes = 13-byte roundtrip, empty block `00`, short output buffer, both modules. Build/ABI evidence only, not codec verification or a differential suite.

## Codex session harness

Task input dir = only material that arm receives; no symlinks. Copy excludes `.git`, `.codex`, `.agents`, `.claude`, `.claude.json`, `.mcp.json`, AGENTS.md/AGENTS.override.md, CLAUDE.md/CLAUDE.local.md. MAIN supplies requirement prose. Prompt file is copied byte-for-byte; its text is passed as one argument, with stdin closed.

```sh
export FVA_BENCH_MODEL='<protocol model ID>'
export FVA_BENCH_EFFORT='<protocol reasoning effort>'
export FVA_BENCH_SECONDS='<pilot-derived positive integer>'
export FVA_BENCH_AUTH_FILE='<absolute path to the selected Codex auth.json>'
bench/harness/run-session --dry-run bare lz4-c 1 2-3 /path/prompt.txt /path/inputs
```

Arms = bare/prompted/tool/fva; index starts at 1. Dry-run creates nothing and prints the exact launch/environment + auth-copy command, never auth bytes. Remove `--dry-run` only for MAIN's rubric-authorized launches. Existing run IDs fail rather than overwrite. No Claude backend remains.

### Isolation / capture contract

- Work root = `$HOME/.cache/fva-bench/runs/<arm>-<task>-<n>/work`; fresh git repo, HOME, CODEX_HOME, XDG dirs, tmp. Only supplied task inputs are copied, no enclosing repo/history.
- CODEX_HOME starts with only the selected auth.json (mode 600). No global config, AGENTS.md, skills, MCP configuration, history, or user rules copied. Copied auth is removed on exit; original auth untouched. No real credentials were read/copied by prep tests.
- `env -i` forwards only explicit HOME/CODEX_HOME/PATH/locale/temp/git controls; parent model/provider/API-key/shell-startup variables are absent. Auth comes from the selected file, not ambient API keys.
- Launch = `codex exec -C <work> -s workspace-write --json --ephemeral --ignore-user-config --ignore-rules`; explicit model/reasoning effort, `approval_policy="never"`, `project_doc_max_bytes=0`; prompt argument + `< /dev/null`. Instructions/rules are disabled for this isolated benchmark session, not the development session.
- Codex's workspace-write sandbox is not an adversarial read-visibility boundary. Administrative policy/default features still apply. MAIN chooses whether host filesystem/network isolation beyond this is necessary, and verifies actual sandbox/tool behavior in the pilot.
- Default child PATH = `/usr/local/bin:/usr/bin:/bin`; `FVA_BENCH_PATH` supplies approved tool bins. Codex resolves from caller PATH; metadata records launch-file SHA256 + `codex --version` (the SHA is of that file, not every dynamically loaded CLI component).
- taskset checks effective affinity equals the requested CPU set. Timeout = TERM at the wall cap, KILL after 30 s. Exit 124 = timeout; 137 = killed, not assumed to prove a timeout cause.
- Outputs = prompt.txt, inputs.sha256, command.sh (auth path only), metadata.json, raw stdout.jsonl, stderr.log, parser.log, result.json, live work/. Result = status, runner/agent rc, elapsed wall duration, thread ID, started/completed/failed turns, the last completed event's cumulative input/output/cache-read/cache-write/reasoning counters.
- Codex 0.163.0 emits cumulative thread totals: take the last completed snapshot, never sum snapshots. Cached input is a subset, not added to total input again. Missing optional cache-write/reasoning counters → null. API duration/dollar cost are not supplied → null; MAIN derives cost under the rubric. Malformed/incomplete/failed/timeout runs retain logs. The last observed usage remains available with `usage_complete:false`; missing usage stays null, not invented zeros.

Coverage = 8 mock streams: success, turn failure, malformed JSON, process failure, timeout, missing terminal event, invalid usage, partial usage then failure; auth-only CODEX_HOME + auth cleanup, closed stdin, config exclusion, cleared parent routing, dry-run side effects/secrets, overwrite refusal. Live Codex auth/config/sandbox/event compatibility remain a pilot check: prep runs no real Codex or Claude session.

## Decisions for MAIN

1. Exact model + reasoning effort, feature/subagent/tool policy, CPU allocation, run order, repetitions, pilot-derived wall cap. Keep comparison conditions equal where the rubric requires it.
2. Selected auth file/billing method, Codex version/native components, model access; token-to-cost method (stream has no dollar figure).
3. Additional filesystem/network isolation; toolchain/solver exposure without leaking FVA sources, rubric, or other arms' outputs. Pilot default workspace-write network behavior.
4. FVA arm's history-free root-package export/cache/guide + commit; curated task inputs + baseline wrappers.
5. Compiled-core boundaries, claims, API preconditions, source/shim/compiler trust accounting. Build smokes do not set the proof contract.
6. Frama-C provers/options + Verus library access; source adaptation costs; acceptance of the explicit 33.0-bundle/pinned 32.1-userland composition.
7. Gate integration: `check-prep`, bench shell lint, where expensive tool/build smokes run. MAIN owns `.agent/`, `.claude/rules/`, `scripts/gate`, `.gitignore` changes.

## Source excerpts

- [Verus release](https://github.com/verus-lang/verus/releases/tag/release/0.2026.10.18.7d82994): `Release 0.2026.10.18.7d82994`. [Toolchain](https://raw.githubusercontent.com/verus-lang/verus/7d82994/rust-toolchain.toml): `channel = "1.99.1"`.
- [Frama-C install](https://frama-c.com/html/get-frama-c.html): `chmod +x frama-c-linux-x86-64-33.0-Arsenic.run`. Asset checksum is locally measured; digest pins in fetch script.
- [Codex noninteractive](https://developers.openai.com/codex/noninteractive): “Use `--ignore-user-config` when you need a run that doesn’t load `$CODEX_HOME/config.toml`, and `--ignore-rules` when you need to skip user and project execpolicy `.rules` files for a controlled automation environment.” “When you enable `--json`, `stdout` becomes a JSON Lines (JSONL) stream”. Sample: `{"type":"turn.completed","usage":{"input_tokens":24763,"cached_input_tokens":24448,"output_tokens":122,"reasoning_output_tokens":0}}`.
- [Codex 0.163.0 event implementation](https://github.com/openai/codex/blob/rust-v0.163.0/codex-rs/exec/src/event_processor_with_jsonl_output.rs#L118-L127): `input_tokens: usage.total.input_tokens`, `cache_write_input_tokens: usage.total.cache_write_input_tokens`; TurnCompleted emits `usage: self.usage_from_last_total()`.
- [Codex instructions](https://developers.openai.com/codex/guides/agents-md): “In your Codex home directory (defaults to `~/.codex`, unless you set `CODEX_HOME`), Codex reads `AGENTS.override.md` if it exists. Otherwise, Codex reads `AGENTS.md`.” Project discovery starts at the Git root. “Codex skips empty files and stops adding files once the combined size reaches the limit defined by `project_doc_max_bytes`”.
