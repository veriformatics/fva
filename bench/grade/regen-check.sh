#!/usr/bin/env bash
# M2 (a) link check for runs whose own script derives files from the pinned artifact: copy the
# archived work dir + the artifact, regenerate (REGEN) and cmp each listed file with the archive,
# then plant a one-digit change per file and expect CHECK to fail. Usage: regen-check.sh TASK
# ARTIFACT TSV (run<TAB>regen cmd<TAB>check cmd<TAB>file,file…). Prints one line per file.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 artifact=$(realpath -e "$2") tsv=$3
R=$FVA_GRADE_OUT/regen/$task
mkdir -p "$R"
while IFS=$'\t' read -r r regen check files; do
	[[ -z $r || $r == \#* ]] && continue
	rm -rf "${R:?}/$r"
	rsync -a --exclude .lake "bench/runs/$r/work/" "$R/$r/"
	cp "$artifact" "$R/$r/"
	IFS=, read -ra fs <<<"$files"
	for f in "${fs[@]}"; do rm -f "$R/$r/$f"; done
	(cd "$R/$r" && timeout 600 bash -c "$regen") >"$R/$r.regen.log" 2>&1
	rrc=$?
	for f in "${fs[@]}"; do
		cmp -s "$R/$r/$f" "bench/runs/$r/work/$f"
		c=$?
		cp "bench/runs/$r/work/$f" "$R/$r/$f"
		sed -i '0,/[0-9]/s/\([0-9]\)/\1\1/' "$R/$r/$f"
		(cd "$R/$r" && timeout 600 bash -c "$check") >"$R/$r.planted.log" 2>&1
		prc=$?
		cp "bench/runs/$r/work/$f" "$R/$r/$f"
		(cd "$R/$r" && timeout 600 bash -c "$check") >"$R/$r.clean.log" 2>&1
		crc=$?
		printf '%s\t%s\tregen rc=%s\tcmp=%s\tclean check rc=%s\tplanted check rc=%s\n' "$r" "$f" "$rrc" "$c" "$crc" "$prc"
	done
done <"$tsv"
