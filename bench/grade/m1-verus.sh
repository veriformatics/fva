#!/usr/bin/env bash
# M1 for a Verus tool arm: rebuild each run, rerun each Verus command the run documents with the
# runs' Verus (~/.cache/fva-bench/bin/verus). Usage: m1-verus.sh TASK CMDS.tsv (run<TAB>verus
# arguments, workdir-relative). Appends to ~/.cache/fva-bench/grade/TASK/m1-tool.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 cmds=$2
G=$FVA_GRADE_OUT/$task
mkdir -p "$G"
out=$G/m1-tool.tsv
in=$FVA_BENCH_HOME/inputs/$task/tool-$task
declare -A built=()
while IFS=$'\t' read -r r args; do
	[[ -z $r || $r == \#* ]] && continue
	if [[ -z ${built[$r]:-} ]]; then
		rm -rf "${G:?}/$r"
		bench/grade/rebuild "$in" "bench/runs/$r" "$G/$r" >/dev/null 2>&1 || {
			printf '%s\t%s\trebuild failed\n' "$r" "$args" >>"$out"
			continue
		}
		built[$r]=1
	fi
	read -ra a <<<"$args"
	file=
	for arg in "${a[@]}"; do [[ $arg != *.rs ]] || file=$arg; done
	[[ -n $file ]] || exit 2
	log=$G/$r.$(basename "$file").verus.log
	(cd "$G/$r" && "$FVA_BENCH_HOME/bin/verus" "${a[@]}") >"$log" 2>&1
	rc=$?
	printf '%s\t%s\trc=%s\t%s\n' "$r" "$args" "$rc" "$(grep -E 'verification results' "$log" | tail -1)" >>"$out"
done <"$cmds"
