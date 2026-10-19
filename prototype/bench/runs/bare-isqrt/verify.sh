#!/bin/sh
# Offline: only the installed Lean standard library is used.
set -eu
cd "$(dirname "$0")"
lake build
# Re-elaborate the proof sources and source pin, without relying on build caches.
lake env lean -DwarningAsError=true ./Isqrt.lean
lake env lean -DwarningAsError=true ./Machine.lean
lake env lean -DwarningAsError=true ./Check.lean
