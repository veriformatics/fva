#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
exec lake env python3 verify.py
