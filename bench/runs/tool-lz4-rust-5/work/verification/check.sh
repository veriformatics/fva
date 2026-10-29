#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
verus --version
verus --no-cheating verification/decoder.rs
verus --no-cheating --rlimit 60 verification/optimized.rs
verus --no-cheating verification/monitor.rs
python3 verification/replay.py
bash verification/rebuild.sh
printf '%s\n' 'PASS: model proofs, finite artifact replays, and byte-identical rebuild'
