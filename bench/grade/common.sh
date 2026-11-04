#!/usr/bin/env bash
# Sourced by grading drivers; archived checks keep their original languages and commands.
set -uo pipefail
grade_dir=$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")
repo=$(realpath -e "$grade_dir/../..")
export FVA_GRADE_DIR=$grade_dir
export FVA_BENCH_HOME=${FVA_BENCH_HOME:-$HOME/.cache/fva-bench}
export FVA_GRADE_OUT=${FVA_GRADE_OUT:-$repo/.scratch/grade}
mkdir -p "$FVA_GRADE_OUT"
FVA_GRADE_OUT=$(realpath -e "$FVA_GRADE_OUT")
export FVA_GRADE_OUT
export FVA_GRADE_BIN=$FVA_GRADE_OUT/bin
mkdir -p "$FVA_GRADE_BIN"
# Frama-C must use the grading wrapper, rather than the batch's broker shim.
shim=$(mktemp "$FVA_GRADE_BIN/.frama-c.XXXXXXXX")
printf '#!/usr/bin/env bash\nexec %q "$@"\n' "$repo/bench/tools/frama-c" >"$shim"
chmod +x "$shim"
mv -Tf "$shim" "$FVA_GRADE_BIN/frama-c"
# The repo's pinned tools (wasm-tools, wasmtime) when the bench root has none (CI, fresh hosts).
export PATH=$FVA_GRADE_BIN:$FVA_BENCH_HOME/bin:$repo/.tools/bin:$PATH
cd "$repo" || exit 2
