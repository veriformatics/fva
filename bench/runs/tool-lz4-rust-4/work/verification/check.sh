#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
verus --version
verus verification/entry.rs --no-cheating
python3 verification/check_entry.py
verus verification/bounds.rs --no-cheating
verus verification/decoder.rs --no-cheating
python3 verification/check_artifact.py
