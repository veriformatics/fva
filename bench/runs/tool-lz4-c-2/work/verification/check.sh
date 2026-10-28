#!/usr/bin/env bash
# Run from the project root. Fail if a completed proof or finite check fails.
set -euo pipefail
python3 verification/lift.py
wasm-tools validate lz4-c.wasm
frama-c --check-wp . verification/early.c verification/memory.c \
  -wp -wp-rte -wp-prover qed,alt-ergo -wp-timeout 5
clang --target=wasm32 -O2 -nostdlib -ffreestanding -fno-builtin \
  -DLIFT_RUNTIME -Wl,--no-entry -Wl,--export-memory \
  -Wl,--export=f2 -Wl,--export=getmem \
  verification/lifted.c verification/memory.c -o verification/lifted.wasm
python3 verification/instrument.py
node verification/test.mjs
