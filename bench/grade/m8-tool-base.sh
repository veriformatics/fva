#!/usr/bin/env bash
# Clean baseline (C0) of each tool run's documented check on a copy of its rebuilt project.
# Usage: m8-tool-base.sh TASK TSV [CMD_FIELD] (run<TAB>…; the check = field CMD_FIELD, default 4 =
# the Verus manifests' run<TAB>file<TAB>FN<TAB>cmd<TAB>site, 3 = T2's run<TAB>file<TAB>cmd; one C0
# per run) → GRADE/TASK/m8-tool-base.tsv
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 tab=$2 col=${3:-4}
G=$FVA_GRADE_OUT/$task
out=$G/m8-tool-base.tsv
: >"$out"
export PATH=$FVA_GRADE_BIN:$FVA_BENCH_HOME/bin:$PATH
declare -A seen=()
while IFS=$'\t' read -ra f; do
	r=${f[0]:-}
	[[ -z $r || $r == \#* || -n ${seen[$r]:-} ]] && continue
	seen[$r]=1
	cmd=${f[col - 1]:?}
	w=$G/$r.C0-clean
	rm -rf "${w:?}"
	cp -a "$G/$r" "$w"
	(cd "$w" && timeout 3600 bash -c "$cmd") >"$w.log" 2>&1
	printf '%s\tC0-clean\trc=%s\n' "$r" "$?" >>"$out"
done <"$tab"
