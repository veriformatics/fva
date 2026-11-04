#!/usr/bin/env bash
# M8 for the T2 tool arm: bench/grade/inject-tool per run (rebuilt dir from m1-wp.sh) on its main WP file, the run's
# documented check; frama-c = the real wrapper (grading shim bin-tool). → GRADE/lz4-c/m8-tool.tsv
# Caveat: checks that regenerate the planted file (prepare.py / lift.py) can overwrite the cheat → read misses' logs.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
G=$FVA_GRADE_OUT/lz4-c
tab=bench/grade/manifests/m8-tool-lz4-c.tsv
export PATH=$FVA_GRADE_BIN:$FVA_BENCH_HOME/bin:$PATH
: >"$G/m8-tool.tsv"
while IFS=$'\t' read -r r file cmd; do
	bench/grade/inject-tool "$G/$r" "$file" lz4-c.wasm "$cmd" "$G/$r.m8" >"$G/$r.m8.log" 2>&1
	while IFS= read -r l; do printf '%s\t%s\n' "$r" "$l"; done < <(grep -E '^C[0-4]' "$G/$r.m8.log") >>"$G/m8-tool.tsv"
	echo "$(date +%T) $r m8-tool done" >>"$G/progress.log"
done <"$tab"
