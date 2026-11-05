#!/usr/bin/env bash
# Runs the string-baseline benchmark matrix, one process per (job, tool, length, alphabet,
# regime, k) cell, and writes a TSV file.
#
# Usage: run_matrix.sh <bench-binary> <out.tsv> <exact|bounded|all>
#
# Each cell runs pinned to CPU 0 with a 60 second wall-clock limit and a 6 GiB address-space
# limit. A cell that hits either limit is recorded as `timeout` with the reason. The 1-minute
# load average is recorded at the start of each cell.
set -u

BIN=$1
OUT=$2
JOB=${3:-all}
ERR="$OUT.stderr"

# Every list can be narrowed through the environment, for example to re-run a subset of the matrix.
LENS=${STRB_LENS:-"16 100 1000 10000 100000"}
ALPHS=${STRB_ALPHS:-"2 4 256 sparse"}
TOOLS=${STRB_TOOLS:-"edlib wfa rapidfuzz difffold"}
BOUNDED_REGIMES=${STRB_BOUNDED_REGIMES:-"d<k d==k d==k+1 d>>k tiny-prefix-suffix unrelated"}
EXACT_REGIMES=${STRB_EXACT_REGIMES:-"tiny-prefix-suffix d=16 unrelated"}
KS=${STRB_KS:-"1 2 4 8 32 128"}

printf 'job\ttool\tlen\talphabet\tregime\tk\tdesigned_d\tpairs\tgood_pairs\tstatus\toracle\trealized_d_median\tmismatches\tmin_us_per_pair\tmed_us_per_pair\tmax_us_per_pair\tnote\tload1_at_start\n' > "$OUT"
: > "$ERR"

cell() {
	# Arguments are the bench flags for one cell.
	local load prefix pairs line rc
	load=$(cut -d' ' -f1 /proc/loadavg)
	# Describe the cell first, so a timed-out run still has the labelled prefix.
	prefix=$("$BIN" --describe "$@") || { echo "describe failed: $*" >&2; return; }
	pairs=$(printf '%s' "$prefix" | cut -f8)
	line=$( (ulimit -v 6291456; timeout 60 taskset -c 0 "$BIN" "$@") 2>>"$ERR" )
	rc=$?
	if [ $rc -eq 124 ]; then
		line="${prefix}"$'\t0\ttimeout\t-\t-\t-\t-\t-\t-\texceeded 60 s wall-clock limit'
	elif [ $rc -ne 0 ] || [ -z "$line" ]; then
		line="${prefix}"$'\t0\tfailed\t-\t-\t-\t-\t-\t-\t'"exit code $rc"
	fi
	printf '%s\t%s\n' "$line" "$load" >> "$OUT"
}

if [ "$JOB" = "bounded" ] || [ "$JOB" = "all" ]; then
	for len in $LENS; do
		pairs=5; [ "$len" -ge 10000 ] && pairs=3
		for alph in $ALPHS; do
			for regime in $BOUNDED_REGIMES; do
				for k in $KS; do
					for tool in $TOOLS; do
						cell --job bounded --tool "$tool" --len "$len" --alphabet "$alph" --regime "$regime" --k "$k" --pairs "$pairs" --reps 7
					done
				done
			done
		done
	done
fi

if [ "$JOB" = "exact" ] || [ "$JOB" = "all" ]; then
	for len in $LENS; do
		pairs=5; [ "$len" -ge 10000 ] && pairs=3
		for alph in $ALPHS; do
			for regime in $EXACT_REGIMES; do
				for tool in $TOOLS; do
					cell --job exact --tool "$tool" --len "$len" --alphabet "$alph" --regime "$regime" --pairs "$pairs" --reps 7
				done
			done
		done
	done
fi
