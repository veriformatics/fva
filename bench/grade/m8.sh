#!/usr/bin/env bash
# M8 for one task: per run (rebuilt dir from m1.sh), inject C1–C4 into the first claimed theorem
# outside a Lifted module and run the run's documented check (CMDS file: run<TAB>cmd).
# Usage: m8.sh TASK CMDS ARTIFACT RUN... ; writes ~/.cache/fva-bench/grade/TASK/m8.tsv.
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 cmds=$2 artifact=$3
shift 3
G=$FVA_GRADE_OUT/$task
export PATH=$FVA_BENCH_HOME/bin:$PATH
for r in "$@"; do
	cmd=$(awk -F'\t' -v r="$r" '$1==r {print $2}' "$cmds")
	line=$(grep -v -P '\.Lifted\t' "$G/$r.claims" | grep -v -E '^\.|^(Proofs\.)?GradeObservation' | head -1)
	mod=${line%%	*}
	thm=${line#*	}
	file=${mod//.//}.lean
	if [[ -z $cmd || -z $line ]]; then
		printf '%s\t-\tno cmd or theorem\n' "$r" >>"$G/m8.tsv"
		continue
	fi
	bench/grade/inject "$G/$r" "$file" "$thm" "$artifact" "$cmd" "$G/$r.m8" >"$G/$r.m8.log" 2>&1
	while IFS= read -r l; do printf '%s\t%s\n' "$r" "$l"; done < <(grep -E '^C[1-4]' "$G/$r.m8.log") >>"$G/m8.tsv"
	echo "$(date +%T) $r m8 done" >>"$G/progress.log"
done
