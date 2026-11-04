#!/usr/bin/env bash
# M8 for a Verus tool arm: bench/grade/inject-tool per row (rebuilt dir from m1-verus.sh), the run's documented check.
# Usage: m8-tool-verus.sh TASK TSV (run<TAB>file<TAB>FN<TAB>cmd<TAB>site) → GRADE/TASK/m8-tool.tsv (run, site, FN, cheat rows).
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 tab=$2
G=$FVA_GRADE_OUT/$task
export PATH=$FVA_BENCH_HOME/bin:$PATH
while IFS=$'\t' read -r r file fn cmd site; do
	[[ -z $r || $r == \#* ]] && continue
	bench/grade/inject-tool "$G/$r" "$file" lz4-flex.wasm "$cmd" "$G/$r.$site" "$fn" >"$G/$r.$site.log" 2>&1
	while IFS= read -r l; do printf '%s\t%s\t%s\t%s\n' "$r" "$site" "$fn" "$l"; done < <(grep -E '^C[0-4]' "$G/$r.$site.log") >>"$G/m8-tool.tsv"
	echo "$(date +%T) $r $site m8-tool done" >>"$G/progress.log"
done <"$tab"
