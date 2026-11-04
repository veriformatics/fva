#!/usr/bin/env bash
# M8 alternative planting (grade README: a first cited theorem in a script-written module → also
# plant at the first cited theorem outside such modules). Usage: m8-alt.sh TASK ARTIFACT ALT.tsv
# (run<TAB>module<TAB>theorem); the run's check command from m8-TASK.tsv; appends GRADE/TASK/m8-alt.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 artifact=$2 alt=$3
G=$FVA_GRADE_OUT/$task
export PATH=$FVA_BENCH_HOME/bin:$PATH
while IFS=$'\t' read -r r mod thm; do
	[[ -z $r || $r == \#* ]] && continue
	cmd=$(awk -F'\t' -v r="$r" '$1==r {print $2}' "bench/grade/manifests/m8-$task.tsv")
	bench/grade/inject "$G/$r" "${mod//.//}.lean" "$thm" "$artifact" "$cmd" "$G/$r.m8alt" >"$G/$r.m8alt.log" 2>&1
	while IFS= read -r l; do printf '%s\t%s\t%s\n' "$r" "$thm" "$l"; done < <(grep -E '^C[1-3]' "$G/$r.m8alt.log") >>"$G/m8-alt.tsv"
done <"$alt"
