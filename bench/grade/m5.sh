#!/usr/bin/env bash
# M5 statement closure per run (bench/grade/Surface.lean over the claimed theorems, every claimed
# module imported). Usage: m5.sh TASK RUN... → GRADE/TASK/m5.tsv (run, decl rows, total, shared).
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1
shift
G=$FVA_GRADE_OUT/$task
out=$G/m5.tsv
[[ ${GRADE_APPEND:-} ]] || : >"$out"
for r in "$@"; do
	mods=$(cut -f1 "$G/$r.claims" | sort -u | paste -sd,)
	mapfile -t ths < <(cut -f2 "$G/$r.claims")
	project=$G/$r
	[[ ! -d $G/$r.observation ]] || project=$G/$r.observation
	(cd "$project" && timeout 900 nice -n 19 lake env lean --run "$grade_dir/Surface.lean" "$project" "$mods" "${ths[@]}") >"$G/$r.m5" 2>&1
	rc=$?
	while IFS= read -r l; do printf '%s\t%s\n' "$r" "$l"; done <"$G/$r.m5" >>"$out"
	printf '%s\trc\t%s\n' "$r" "$rc" >>"$out"
done
