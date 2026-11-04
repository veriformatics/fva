#!/usr/bin/env bash
# Per-batch-slice heavy grading after m1.sh has rebuilt the runs: M5 closures, M8 + clean
# baselines, appending to the task's tables. Usage: grade-rest.sh TASK ARTIFACT RUN...
set -uo pipefail
# shellcheck source=bench/grade/common.sh
source "$(dirname "$(realpath -e "${BASH_SOURCE[0]}")")/common.sh"
task=$1 artifact=$2
shift 2
G=$FVA_GRADE_OUT/$task
export GRADE_APPEND=1
bench/grade/m5.sh "$task" "$@" >/dev/null 2>&1
echo "$(date +%T) m5 done: $*" >>"$G/progress.log"
bench/grade/m8.sh "$task" "bench/grade/manifests/m8-$task.tsv" "$artifact" "$@" >/dev/null 2>&1
echo "$(date +%T) m8 done: $*" >>"$G/progress.log"
bench/grade/m8-base.sh "$task" "bench/grade/manifests/m8-$task.tsv" "$@" >/dev/null 2>&1
echo "$(date +%T) m8-base done: $*" >>"$G/progress.log"
