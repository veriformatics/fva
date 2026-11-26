# WASI probes (pinned `.tools/bin/wasmtime` 50.0.0 ebe5e8df1, Linux, `/tmp` = tmpfs)

Evidence the WASI model cites (`FVA/Spec/Wasi/*` docstrings, `FVA/Proof/Wasi/Examples.lean`, `docs/contracts/U29a-wasi.md`). The blind corpus's per-vector probes live apart (`FVATest/Wasi/oracle/*.wat`, replayed by `oracle/replay`).

Run: `.tools/bin/wasmtime run [--env K=V] [--dir FS::.] --invoke F PROBE ARGS…`; `FS` = a fresh directory holding `f` = `abc`, `d/`, `e/`. Observed = the invoked function's results in order (`--invoke` prints one per line).

| probe | invocation | observed (50.0.0) | rule it backs |
|---|---|---|---|
| `fd-reuse.wat` | `--dir FS::. --invoke probe` | opens 4, 5, 6; close 4 + 6; next opens → 6, 4 | `E`: the greatest freed fd first (p1:458, 1366) |
| `stdin-chunk.wat` | `--invoke probe`, one 1 MiB iovec on fd 0; stdin = 1 MiB file / 1 MiB pipe / 10 B file | 65536 / 65536 / 10 | `E`: a stdin read returns ≤ 65,536 bytes (`stdinChunk`) |
| `big-transfers.wat` | `--dir FS::. --invoke …` | 1 MiB file read, file write, stdout write → 1048576 each | `E`: files + stdout transfer the whole first buffer |
| `stdin-zero.wat`, `c13/zero-read.wat` | `--invoke probe`, all-empty iovecs on fd 0 | errno 27 (`c13/out-50.0.0/zero-read-*`) | `E`: an empty stdin request → `intr` |
| `c13/{abi,paths,valid-output,wrong-signature}.wat` | consultant-13; per-export outputs in `c13/out-50.0.0/`, `c13/out-50.0.1/` (identical p1) | see the output files | profile (traps on bad pointers), path walk, `Launch` signature check |
| `r5/MemoryEnd.wat` | `--env K=V --dir FS::. --invoke F`, F = `env_end` `pre_end` `random_end` (+ `_control`) | `*_end`: trap `Pointer overflow`; controls: 0 | profile: every region ends below 2^32 |
| `r5/OpenFlags.wat` | `--dir FS::. --invoke probe P 0 R FF 0` (P 1 = `d`, 0 = `f`; R rights) | `d`, R 2, FF 1 or 4 → `0 0 8 0`; `f`, R 74, FF 2/8/16 → `58 0 0 0`; FF 0/1/4 → `0 FF 0 0` (open errno, flags, set_flags errno, flags after) | W pins: a directory keeps no fdflags; a sync fdflag → `notsup` |
| `r5/OffsetIO.wat` | `--dir FS::. --invoke probe ADD N W` (pos 2^63 − 1 + ADD; N bytes; W 0 read / 1 write) | ADD 1: `0 0 0 28` for every N, W; ADD 0: N 1 → `… 28`, N 0 → `0 0 0 0` | `E`: a positioned transfer reaching 2^63 → `inval` |
| `r5/UnlinkedDirectory.wat` | `--dir FS::. --invoke probe 1` (rmdir `e` first) / `0` | `0 0 44 44` / `0 0 0 0` | POSIX rmdir: no entry created in a removed directory |
| `Append.wat` | `--dir FS::. --invoke probe BACK L1 L2 L3` (write L1 at 2^63 − BACK, then append L2, L3) | `10 5 10 1` → `0 5 0 4 22 999 5 5`; `10 5 10 0` → `0 5 0 4 0 0 5 5`; `3 3 1 1` → `28 999 …` | `E`: an append cut at 2^63 − 1 bytes, then `fbig`; a positioned write reaching 2^63 → `inval` (tmpfs: `s_maxbytes` = 2^63 − 1; ext4 refuses at 16 TiB) |
