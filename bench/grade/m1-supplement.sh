#!/usr/bin/env bash
# M1 supplement: check-lean on claimed theorems claims.py missed (MAIN-ruled from claims-review-lz4-c.txt):
# bare-1 stem (_checked), bare-5 file (caseN_checked), fva-5 stem (_holds). Writes GRADE/lz4-c/m1-supplement.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
G=$FVA_GRADE_OUT/lz4-c
out=$G/m1-supplement.tsv
: >"$out"
pick() { awk -v run="$1" -v form="$2" -v pat="$3" '/^[a-z]/ {r=$1; next} r==run {split($0,a,"\t"); sub(/^ +/,"",a[1]); if (a[3]==form && a[2] ~ pat) print a[1] "\t" a[2]}' bench/grade/manifests/claims-review-lz4-c.txt; }
for spec in "bare-lz4-c-1 stem _checked$" "bare-lz4-c-5 file ^case[0-9]+_checked$" "fva-lz4-c-5 stem _holds$"; do
	read -r run form pat <<<"$spec"
	mapfile -t rows < <(pick "$run" "$form" "$pat")
	mapfile -t mods < <(printf '%s\n' "${rows[@]}" | cut -f1 | sort -u)
	for f in "${mods[@]}"; do
		mod=${f%.lean}
		mod=${mod//\//.}
		ns=$(grep -m1 -oP '^\s*namespace\s+\K[A-Za-z_][A-Za-z0-9_.]*' "bench/runs/$run/work/$f" || true)
		mapfile -t ths < <(printf '%s\n' "${rows[@]}" | awk -F'\t' -v f="$f" -v ns="$ns" '$1==f {print (ns == "" ? $2 : ns "." $2)}')
		if bench/grade/check-lean "$G/$run" "$mod" "${ths[@]}" >"$G/$run.$mod.supp.log" 2>&1; then rc=0; else rc=$?; fi
		while IFS= read -r l; do printf '%s\t%s\t%s\n' "$run" "$mod" "$l"; done <"$G/$run.$mod.supp.log" >>"$out"
		printf '%s\t%s\trc=%s\tthms=%s\n' "$run" "$mod" "$rc" "${#ths[@]}" >>"$out"
	done
done
