#!/usr/bin/env bash
# Mutation-check fixture test (U12 E1). Exit status: 0 pass, 1 assertion failure,
# 2 setup/infrastructure (tool.ok absent = a missing tool), 3 crash.
cd "$(dirname "$0")" || exit 2
[[ -e tool.ok ]] || exit 2
out=$(.lake/build/bin/fixtest) || exit 2
read -r dbl slow crashy infra <<<"$out"
[[ $slow == 2 ]] && sleep 600
[[ $crashy == 3 ]] && exit 3
[[ $infra == 5 ]] && exit 2
[[ $dbl == 6 && $slow == 1 && $crashy == 2 && $infra == 4 ]] || exit 1
