#!/usr/bin/env bash
# M2: route-module elaboration, fresh process per run, CPU 2, 1 warm-up + 3 interleaved rounds.
set -u
cd /home/eturkes/Projects/fva
files=(".scratch/u19/m2/B1.lean B1" "FVATest/Subjects/Lz4C/ExtDirect.lean D" "FVATest/Subjects/Lz4C/ExtRefine.lean R"
	".scratch/u19/m2/B2.lean B2" "FVATest/Subjects/Lz4C/O1/ExtDirect.lean O1D"
	".scratch/u19/m2/B3.lean B3" "FVATest/Subjects/Lz4C/O1/ExtRefine.lean O1R")
for round in warm 1 2 3; do
	for spec in "${files[@]}"; do
		set -- $spec
		/usr/bin/time -f "$round $2 wall=%e rss=%M rc=%x" taskset -c 2 lake env lean "$1" >/dev/null 2>> .scratch/u19/m2/times.log
	done
done
echo M2-DONE >> .scratch/u19/m2/times.log
