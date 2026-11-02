#!/usr/bin/env bash
# Mutation-check fixture test (U12 E1). Exit status: 0 pass, 1 assertion failure,
# 2 setup/infrastructure (tool.ok absent = a missing tool), 3 crash.
cd "$(dirname "$0")" || exit 2
[[ -e tool.ok ]] || exit 2
out=$(.lake/build/bin/fixtest) || exit 2
read -r dbl slow crashy hungry infra <<<"$out"
[[ $slow == 2 ]] && sleep 600
[[ $crashy == 3 ]] && exit 3
# 16 MiB per step up to 1 GiB, then a hang: a runner ignoring its memory cap times out instead
if [[ $hungry == 3 ]]; then
	x=
	while ((${#x} < 1 << 30)); do x+=$(printf '%*s' 16777216 ''); done
	sleep 600
fi
[[ $infra == 5 ]] && exit 2
[[ $dbl == 6 && $slow == 1 && $crashy == 2 && $hungry == 2 && $infra == 4 ]] || exit 1
