#!/usr/bin/env bash
# M8 baseline: each run's documented check on its clean rebuilt project (copy), scored as inject
# scores a cheat (rc, named). Usage: m8-base.sh TASK CMDS RUN... → GRADE/TASK/m8-base.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 cmds=$2
shift 2
G=$FVA_GRADE_OUT/$task
out=$G/m8-base.tsv
[[ ${GRADE_APPEND:-} ]] || : >"$out"
export PATH=$FVA_GRADE_BIN:$FVA_BENCH_HOME/bin:$PATH
for r in "$@"; do
	cmd=$(awk -F'\t' -v r="$r" '$1==r {print $2}' "$cmds")
	w=$G/$r.m8/C0-clean
	rm -rf "${w:?}"
	cp -a "$G/$r" "$w"
	(cd "$w" && timeout 3600 bash -c "$cmd") >"$w.log" 2>&1
	rc=$?
	named=no
	grep -qiE 'sorry|fvaCheat|axiom|skipKernelTC|kernel|mismatch|sha256|link' "$w.log" && named=yes
	printf '%s\tC0-clean\trc=%s\tnamed=%s\n' "$r" "$rc" "$named" >>"$out"
done
