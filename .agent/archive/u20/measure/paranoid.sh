#!/usr/bin/env bash
# The --paranoid run set's four extra kernels (FVA/Trust/Replay.lean `kernels` minus the defaults)
# on each finalist's S1–S5 export, arms alternating per kernel: status (rc; lean4lean's declines by
# its output) + wall + max RSS → paranoid.tsv
set -uo pipefail
m=/home/eturkes/Projects/fva/.scratch/u19c2/measure
bin=/opt/lean/bin
o=$m/paranoid
printf 'kernel\ttag\twall_s\tmaxrss_kib\trc\tdecline\n' >"$m/paranoid.tsv"
for k in leanchecker-paranoid lean4lean nanoda con-ron; do
	for t in c-s1-5 d-s1-5; do
		x=$m/$t.export
		case $k in
		leanchecker-paranoid) cmd=("$bin/leanchecker-paranoid" --silent --from-export "$x") ;;
		lean4lean) cmd=("$bin/lean4lean" --import "$x") ;;
		nanoda)
			printf '{"use_stdin":false,"export_file_path":"%s","permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"num_threads":4,"nat_extension":true,"string_extension":true}' "$x" >"$o/$t.nanoda.json"
			cmd=("$bin/nanoda_bin" "$o/$t.nanoda.json") ;;
		con-ron) cmd=("$bin/con-ron" "$x") ;;
		esac
		tf=$(mktemp)
		/usr/bin/time -o "$tf" -f '%e %M' timeout -k 10 1800 "${cmd[@]}" >"$o/$k-$t.out" 2>&1
		rc=$?
		read -r w r < <(tail -1 "$tf")
		rm -f "$tf"
		d=0
		grep -q -E 'deep recursion detected|unknown constant' "$o/$k-$t.out" && d=1
		printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$k" "$t" "$w" "$r" "$rc" "$d" >>"$m/paranoid.tsv"
	done
done
