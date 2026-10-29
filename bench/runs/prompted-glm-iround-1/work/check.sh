#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lake env python3 verification/check.py
