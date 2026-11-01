#!/usr/bin/env bash
# U20 harvest measurements (docs/contracts/U20-proof-scaling.md M2, M3; cost vector (c) (d) (e)).
# Run once every arm is DONE, on a quiet host. Usage: measure.sh [prep|m2|m3|all]
#   prep: per arm, MAIN's acceptance module (example : <Stmt> := Spike<X>.sk), frozen sha256 check,
#         incremental lake build; module list = the arm's new/changed .lean files vs the base.
#   m2:   1 warm-up + 3 fresh `lake env lean <file>` runs per arm module on CPU $CPU, arms
#         interleaved per run index (rotated order); wall s + max RSS KiB + rc → m2.tsv.
#   r2:   round 2 (arms with SegC): MAIN's acceptance `example : SegC := Spike<X>.segC` + axioms,
#         export of the segC root → bytes + time, leanchecker + con-leche ×3 → r2.tsv.
#   m3:   per arm: export of s1…s5 (+ cumulative s1…sk, from the final commit) → bytes + time;
#         leanchecker + con-leche replays of the s1…s5 export ×3 → time + RSS + rc; the baseline
#         (the frozen statements alone) exported + replayed the same way → m3.tsv.
set -uo pipefail
root=/home/eturkes/Projects/fva
out=$root/.scratch/u19c2/measure
base=c736868
cpu=${CPU:-7}
arms=(d v c)
declare -A wt=([d]=$root/.scratch/worktrees/spike-d [v]=$root/.scratch/worktrees/spike-v
	[c]=$root/.scratch/worktrees/spike-c)
declare -A ns=([d]=SpikeD [v]=SpikeV [c]=SpikeC)
stmts=(MemcpyS1 MemmoveS2 LitWildS3 MatchWildS4 ShortcutS5)
sha_copy=5caf05ac56598440e5b7ee1f58db72c03f41badb7a3ea6342713abb622d57461
sha_short=fc29768f1e15cd5aa491ac07e6ba9cd41c2c963f26fb9f51397905e0bf09113e
sha_seg=ff4cbe5871a98c2adaa946554a44918e6ff93c0120ac93004348fa0cf8077001
mkdir -p "$out"

modname() { local f=${1%.lean}; echo "${f//\//.}"; }

tm() { # cpu cmd… → "wall_s maxrss_kib rc"; GNU time writes to -o, so discarding the command's
	# stderr keeps the measurement (a 2>/dev/null around /usr/bin/time swallows it)
	local c=$1 tf rc
	shift
	tf=$(mktemp)
	taskset -c "$c" /usr/bin/time -o "$tf" -f '%e %M' "$@" >/dev/null 2>&1
	rc=$?
	printf '%s %s\n' "$(tail -1 "$tf")" "$rc"
	rm -f "$tf"
}

prep() {
	local a=$1 w=${wt[$1]} n=${ns[$1]}
	[[ $(sha256sum "$w/FVATest/Subjects/Lz4C/Copy.lean" | cut -d' ' -f1) == "$sha_copy" ]] ||
		{ echo "prep $a: Copy.lean changed"; return 1; }
	[[ $(sha256sum "$w/FVATest/Subjects/Lz4C/Short.lean" | cut -d' ' -f1) == "$sha_short" ]] ||
		{ echo "prep $a: Short.lean changed"; return 1; }
	git -C "$w" diff --name-only --diff-filter=AM "$base"..HEAD -- '*.lean' |
		grep -v 'MainAccept' >"$out/modules-$a.txt"
	# the modules defining s1…s5
	local imports=() k
	for k in 1 2 3 4 5; do
		local f
		f=$(cd "$w" && grep -rl --include='*.lean' -E "^theorem s$k\b" "FVATest/Subjects/Lz4C/$n" | head -1)
		[[ -n $f ]] || { echo "prep $a: no theorem s$k"; return 1; }
		imports+=("$(modname "$f")")
	done
	{
		printf 'import %s\n' "${imports[@]}" | sort -u
		printf '\nnamespace Subjects.Lz4C.%s.MainAccept\n\nopen Subjects.Lz4C\n\n' "$n"
		for k in 1 2 3 4 5; do
			printf 'example : %s := Subjects.Lz4C.%s.s%s\n' "${stmts[$((k - 1))]}" "$n" "$k"
			printf '#print axioms Subjects.Lz4C.%s.s%s\n' "$n" "$k"
		done
		printf '\nend Subjects.Lz4C.%s.MainAccept\n' "$n"
	} >"$w/FVATest/Subjects/Lz4C/$n/MainAccept.lean"
	(cd "$w" && lake --wfail build "FVATest.Subjects.Lz4C.$n.MainAccept" -v >"$out/prep-$a.log" 2>&1)
	local rc=$?
	echo "prep $a: rc=$rc modules=$(wc -l <"$out/modules-$a.txt")" \
		"axioms=$(grep MainAccept "$out/prep-$a.log" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")/5"
	return "$rc"
}

m2() {
	printf 'run\tarm\tmodule\twall_s\tmaxrss_kib\trc\n' >"$out/m2.tsv"
	local r a f i
	for r in 0 1 2 3; do
		local order=("${arms[@]:$((r % 3))}" "${arms[@]:0:$((r % 3))}")
		for a in "${order[@]}"; do
			while read -r f; do
				local w m
				read -r w m i < <(cd "${wt[$a]}" && tm "$cpu" lake env lean "$f")
				printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$r" "$a" "$(modname "$f")" \
					"$w" "$m" "$i" >>"$out/m2.tsv"
			done <"$out/modules-$a.txt"
		done
	done
}

timed() { # label cmd… → appends label, wall, rss, rc to $tsv (default m3.tsv)
	local label=$1 w m rc
	shift
	read -r w m rc < <(tm "$cpu" "$@")
	printf '%s\t%s\t%s\t%s\n' "$label" "$w" "$m" "$rc" >>"$out/${tsv:-m3.tsv}"
}

xport() { # tag dir module roots… → $out/<tag>.export + one export row (CPU-pinned, GNU time)
	local tag=$1 dir=$2 mod=$3 w m rc
	shift 3
	read -r w m rc < <(cd "$dir" && export X="$out/$tag.export" && tm "$cpu" \
		bash -c 'lake env leanexport "$0" -- "$@" >"$X"' "$mod" "$@")
	printf '%s\texport\t1\t%s\t%s\t%s\t%s\n' "$tag" "$(wc -c <"$out/$tag.export")" "$w" "$m" \
		"$rc" >>"$out/${tsv:-m3.tsv}"
}

replays() { # tag… → 3 rounds; each round runs every tag (rotated order) through both checkers,
	# so host drift spreads over the arms instead of landing on one arm's contiguous batch
	local tags=("$@") n=$# r i t x bin
	bin=$(dirname "$(readlink -f "$(command -v lean)")")
	for r in 1 2 3; do
		for ((i = 0; i < n; i++)); do
			t=${tags[$(((i + r) % n))]}
			x=$out/$t.export
			timed "$t	leanchecker	$r	$(wc -c <"$x")" "$bin/leanchecker" --silent --from-export "$x"
			timed "$t	con-leche	$r	$(wc -c <"$x")" "$bin/con-leche" "$x"
		done
	done
}

m3() {
	printf 'tag\tchecker\trep\tbytes\twall_s\tmaxrss_kib\trc\n' >"$out/m3.tsv"
	local a k j roots
	xport baseline "$root" FVATest.Subjects.Lz4C.Short "${stmts[@]/#/Subjects.Lz4C.}"
	for a in "${arms[@]}"; do
		for k in 1 2 3 4 5; do
			roots=()
			for j in $(seq 1 "$k"); do roots+=("Subjects.Lz4C.${ns[$a]}.s$j"); done
			xport "$a-s1-$k" "${wt[$a]}" "FVATest.Subjects.Lz4C.${ns[$a]}.MainAccept" "${roots[@]}"
		done
	done
	replays baseline d-s1-5 v-s1-5 c-s1-5
}

declare -A r2base=([c]=2588dcc [d]=1148d68)

r2() {
	printf 'tag\tchecker\trep\tbytes\twall_s\tmaxrss_kib\trc\n' >"$out/r2.tsv"
	local a tsv=r2.tsv tags=()
	for a in c d; do
		local w=${wt[$a]} n=${ns[$a]} f
		[[ $(sha256sum "$w/FVATest/Subjects/Lz4C/Seg.lean" | cut -d' ' -f1) == "$sha_seg" ]] ||
			{ echo "r2 $a: Seg.lean changed"; continue; }
		f=$(cd "$w" && grep -rl --include='*.lean' -E "^theorem segC\b" "FVATest/Subjects/Lz4C/$n" | head -1)
		[[ -n $f ]] || { echo "r2 $a: no theorem segC"; continue; }
		{
			printf 'import %s\n\nopen Subjects.Lz4C\n\n' "$(modname "$f")"
			printf 'example : SegC := Subjects.Lz4C.%s.segC\n' "$n"
			printf '#print axioms Subjects.Lz4C.%s.segC\n' "$n"
		} >"$w/FVATest/Subjects/Lz4C/$n/MainAcceptR2.lean"
		(cd "$w" && lake --wfail build "FVATest.Subjects.Lz4C.$n.MainAcceptR2" -v >"$out/r2-prep-$a.log" 2>&1)
		echo "r2 $a: accept rc=$? axioms=$(grep MainAcceptR2 "$out/r2-prep-$a.log" |
			grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")/1"
		xport "$a-segC" "$w" "FVATest.Subjects.Lz4C.$n.MainAcceptR2" "Subjects.Lz4C.$n.segC"
		tags+=("$a-segC")
	done
	replays "${tags[@]}"
	# M2 for the round-2 modules (the files each arm's round-2 commit added): 1 warm-up + 3 runs,
	# arm order alternating per run
	printf 'run\tarm\tmodule\twall_s\tmaxrss_kib\trc\n' >"$out/r2-m2.tsv"
	local r g m i ord
	for r in 0 1 2 3; do
		ord=(c d)
		((r % 2)) && ord=(d c)
		for a in "${ord[@]}"; do
			while read -r f; do
				read -r g m i < <(cd "${wt[$a]}" && tm "$cpu" lake env lean "$f")
				printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$r" "$a" "$(modname "$f")" "$g" "$m" "$i" \
					>>"$out/r2-m2.tsv"
			done < <(git -C "${wt[$a]}" diff --name-only --diff-filter=AM "${r2base[$a]}"..HEAD -- '*.lean')
		done
	done
}

m2arm() { # arm cpu → m2-<arm>.tsv: 1 warm-up + 3 fresh runs per module, sequential on that cpu
	local a=$1 c=$2 r f i
	printf 'run\tarm\tmodule\twall_s\tmaxrss_kib\trc\n' >"$out/m2-$a.tsv"
	for r in 0 1 2 3; do
		while read -r f; do
			local w m
			read -r w m i < <(cd "${wt[$a]}" && tm "$c" lake env lean "$f")
			printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$r" "$a" "$(modname "$f")" \
				"$w" "$m" "$i" >>"$out/m2-$a.tsv"
		done <"$out/modules-$a.txt"
	done
}

m2par() { # the arms concurrently, one physical core each (symmetric load); deviation recorded
	m2arm c 1 &
	m2arm d 2 &
	m2arm v 3 &
	wait
}

case ${1:-all} in
prep)
	shift
	for a in "${@:-${arms[@]}}"; do prep "$a"; done
	;;
m2) m2 ;;
m2par) m2par ;;
m3) m3 ;;
r2) r2 ;;
all) for a in "${arms[@]}"; do prep "$a" || exit 1; done && m2 && m3 ;;
esac
