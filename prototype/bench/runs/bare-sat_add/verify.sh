#!/bin/sh
set -eu
cd "$(dirname "$0")"

# Force re-elaboration: include_str/include_binary read the current on-disk files,
# and their dependencies are not inferred by Lake's ordinary source-file cache.
lake clean
lake build
