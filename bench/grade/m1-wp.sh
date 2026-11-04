#!/usr/bin/env bash
# M1 for a Frama-C tool arm: rebuild each run, rerun each WP command the run documents through the
# real wrapper in --check-wp mode (cache off). Usage: m1-wp.sh TASK CMDS.tsv (run<TAB>workdir-relative
# C file<TAB>frama-c options). Writes ~/.cache/fva-bench/grade/TASK/m1-tool.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 cmds=$2
G=$FVA_GRADE_OUT/$task
mkdir -p "$G"
out=$G/m1-tool.tsv
: >"$out"
in=$FVA_BENCH_HOME/inputs/$task/tool-$task
# A run's documented check can generate the files it proves (tool-lz4-c-6: prepare.py writes
# *.annotated.c, which its own .gitignore keeps out of the archive) → run that step after rebuild.
declare -A prep=()
if [[ -f $FVA_GRADE_DIR/manifests/wp-prep-$task.tsv ]]; then
	while IFS=$'\t' read -r r cmd; do prep[$r]=$cmd; done <"$FVA_GRADE_DIR/manifests/wp-prep-$task.tsv"
fi
declare -A built=()
while IFS=$'\t' read -r r file opts; do
	[[ -z $r || $r == \#* ]] && continue
	if [[ -z ${built[$r]:-} ]]; then
		rm -rf "${G:?}/$r"
		bench/grade/rebuild "$in" "bench/runs/$r" "$G/$r" >/dev/null 2>&1 || {
			printf '%s\t%s\trebuild failed\n' "$r" "$file" >>"$out"
			continue
		}
		if [[ -n ${prep[$r]:-} ]] && ! (cd "$G/$r" && bash -c "${prep[$r]}") >"$G/$r.prep.log" 2>&1; then
			printf '%s\t%s\tprepare failed\n' "$r" "$file" >>"$out"
			continue
		fi
		built[$r]=1
	fi
	read -ra o <<<"$opts"
	log=$G/$r.$(basename "$file").wp.log
	bench/tools/frama-c --check-wp "$G/$r" "$file" "${o[@]}" -wp-cache none >"$log" 2>&1
	rc=$?
	printf '%s\t%s\trc=%s\t%s\n' "$r" "$file" "$rc" "$(grep -E 'Proved goals' "$log" | tail -1 | tr -s ' ')" >>"$out"
done <"$cmds"
