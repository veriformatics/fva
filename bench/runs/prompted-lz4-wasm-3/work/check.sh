#!/usr/bin/env bash
set -euo pipefail
exec lake env python3 -E verification/check.py
