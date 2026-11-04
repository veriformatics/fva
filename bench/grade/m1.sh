#!/usr/bin/env bash
# M1: restored inputs + archive → clean builds, axiom scan, two independent kernels.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
[[ $# -ge 2 ]] || exit 2
task=$1
shift
G=$FVA_GRADE_OUT/$task
mkdir -p "$G"
out=$G/m1.tsv
[[ ${M1_APPEND:-} ]] || : >"$out"
for r in "$@"; do
	arm=${r%%-*}
	in=$FVA_BENCH_HOME/inputs/$task/$arm-$task
	observation=$G/$r.observation
	rm -rf "${G:?}/${r:?}" "$observation"
	bench/grade/rebuild "$in" "bench/runs/$r" "$G/$r" >"$G/$r.rebuild.log" 2>&1 || exit 2
	"$grade_dir/claims" "bench/runs/$r/work" >"$G/$r.claims" || exit 2
	if [[ $task == glm-iround ]]; then
		# Generated observations are copied below; hidden forged-proof controls are not claims.
		awk -F '\t' '$1 !~ /^\./' "$G/$r.claims" >"$G/$r.claims.tmp"
		mv "$G/$r.claims.tmp" "$G/$r.claims"
	fi
	if [[ $task == lz4-c ]]; then
		# Nonliteral citations: the reviewed stem/file references in VERIFICATION.md.
		awk -F '\t' -v run="$r" '
			/^[a-z]/ { current=$1; next }
			current==run && ((run=="bare-lz4-c-1" && $3=="stem" && $2 ~ /_checked$/) ||
			(run=="bare-lz4-c-5" && $3=="file" && $2 ~ /^case[0-9]+_checked$/) ||
			(run=="fva-lz4-c-5" && $3=="stem" && $2 ~ /_holds$/)) {
				file=$1; sub(/^ +/,"",file); print file "\t" $2
			}' "$grade_dir/manifests/claims-review-lz4-c.txt" | while IFS=$'\t' read -r file name; do
			ns=$(awk '/^[[:space:]]*namespace / { print $2; exit }' "bench/runs/$r/work/$file")
			mod=${file%.lean}
			printf '%s\t%s%s\n' "${mod//\//.}" "${ns:+$ns.}" "$name"
		done >>"$G/$r.claims"
	fi
	if [[ $r == prompted-glm-iround-1 || $r == prompted-glm-iround-4 ]]; then
		# The documented check produces a claim outside the Lake library.
		cmd=$(awk -F '\t' -v r="$r" '$1==r {print $2}' "$grade_dir/manifests/m8-$task.tsv")
		(cd "$G/$r" && timeout 3600 bash -c "$cmd") >"$G/$r.observation-generate.log" 2>&1 || exit 2
		# The copy stays outside the M8 project: extra #print commands can catch a cheat by name.
		cp -a --reflink=auto "$G/$r" "$observation"
		cp "$observation/.verification/Observation.lean" "$observation/Proofs/GradeObservation.lean"
		name=observation_link
		[[ $r != prompted-glm-iround-1 ]] || name=Observation.r1_failure
		printf 'Proofs.GradeObservation\t%s\n' "$name" >>"$G/$r.claims"
	fi
	mapfile -t mods < <(cut -f1 "$G/$r.claims" | LC_ALL=C sort -u)
	for mod in "${mods[@]}"; do
		mapfile -t ths < <(awk -F '\t' -v m="$mod" '$1==m {print $2}' "$G/$r.claims")
		log=$G/$r.$mod.log
		project=$G/$r
		[[ $mod != Proofs.GradeObservation ]] || project=$observation
		bench/grade/check-lean "$project" "$mod" "${ths[@]}" >"$log" 2>&1
		rc=$?
		# Mixed native_decide/clean exports can reject the clean theorems too: replay separately.
		if grep -q 'con-leche=reject\|leanchecker=reject' "$log" && ((${#ths[@]} > 1)); then
			: >"$log"
			for th in "${ths[@]}"; do
				bench/grade/check-lean "$project" "$mod" "$th" >>"$log" 2>&1
				printf 'individual\t%s\trc=%s\n' "$th" "$?" >>"$log"
			done
		fi
		while IFS= read -r line; do printf '%s\t%s\t%s\n' "$r" "$mod" "$line"; done <"$log" >>"$out"
		printf '%s\t%s\trc=%s\n' "$r" "$mod" "$rc" >>"$out"
	done
	printf '%s\t%s\tm1 done\n' "$(date +%T)" "$r" >>"$G/progress.log"
done
