#!/usr/bin/env bash
# M3: export + per-checker replay of each route theorem (default checkers), memory-capped.
set -u
P=$(lean --print-prefix)
cd /home/eturkes/Projects/fva
for spec in "FVATest.Subjects.Lz4C.ExtDirect Subjects.Lz4C.Direct.ext_l1 D" \
            "FVATest.Subjects.Lz4C.ExtRefine Subjects.Lz4C.Refine.ext_l1 R" \
            "FVATest.Subjects.Lz4C.O1.ExtDirect Subjects.Lz4C.O1.Direct.ext_l1 O1D" \
            "FVATest.Subjects.Lz4C.O1.ExtRefine Subjects.Lz4C.O1.Refine.ext_l1 O1R"; do
  set -- $spec; mod=$1; decl=$2; tag=$3; out=.scratch/u19/m3/final-$tag.export
  taskset -c 3 /usr/bin/time -f "$tag export wall=%e s rss=%M KB rc=%x" lake env "$P/bin/leanexport" "$mod" -- "$decl" > "$out" 2>> .scratch/u19/m3/final-times.log
  echo "$tag export bytes=$(wc -c < "$out")" >> .scratch/u19/m3/final-times.log
  for k in leanchecker con-leche; do
    if [ $k = leanchecker ]; then args=(--silent --from-export "$out"); else args=("$out"); fi
    /usr/bin/time -f "$tag $k wall=%e s rss=%M KB rc=%x" taskset -c 3 systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 "$P/bin/$k" "${args[@]}" > /dev/null 2>> .scratch/u19/m3/final-times.log
  done
done
echo FINAL-DONE >> .scratch/u19/m3/final-times.log
