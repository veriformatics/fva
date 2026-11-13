#!/usr/bin/env bash
# Mutation-check fixture test (U12 E1). Exit status: 0 pass, 1 assertion failure,
# 2 setup/infrastructure (tool.ok absent = a missing tool), 3 crash.
cd "$(dirname "$0")" || exit 2
[[ -e tool.ok ]] || exit 2
out=$(.lake/build/bin/fixtest) || exit 2
read -r dbl slow crashy hungry infra <<<"$out"
[[ $slow == 2 ]] && sleep 600
[[ $crashy == 3 ]] && exit 3
# 512 MiB read in one call, then held by a write blocked on a pipe nobody reads: ≈ 0.05 s CPU
# per 256 MiB, so a starved worker still passes the 256 MiB cap far inside the 10 s stage limit
# (a bash string grown to the cap costs seconds of CPU); a runner ignoring its memory cap times out
if [[ $hungry == 3 ]]; then
	# shellcheck disable=SC2216 # sleep never reads: dd blocks on its write, holding the buffer
	dd if=/dev/zero bs=512M count=1 status=none | sleep 600
fi
[[ $infra == 5 ]] && exit 2
[[ $dbl == 6 && $slow == 1 && $crashy == 2 && $hungry == 2 && $infra == 4 ]] || exit 1
