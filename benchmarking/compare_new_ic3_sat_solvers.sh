#!/bin/sh
# Compare SAT backends for ebmc --new-ic3 on AIGER benchmarks.
# Usage:
#   compare_new_ic3_sat_solvers.sh <timeout-seconds> [benchmark...]
# Environment:
#   BENCH_DIR  directory containing <benchmark>.aig files
#              default: benchmarking/hwmcc08
#   BACKENDS   space-separated backend list
#              default: "ictminisat minisat2 cadical"
#   JOBS       parallel workers for full-directory runs
#              default: 1
# Output:
#   CSV lines: benchmark,backend,seconds,result

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
EBMC=${EBMC:-$SCRIPT_DIR/../src/ebmc/ebmc}
BENCH_DIR=${BENCH_DIR:-$SCRIPT_DIR/hwmcc08}
BACKENDS=${BACKENDS:-"ictminisat minisat2 cadical"}
JOBS=${JOBS:-1}
TIMEOUT=$1
shift

run_one() {
  benchmark=$1
  backend=$2
  file=$BENCH_DIR/$benchmark.aig

  if [ ! -e "$file" ]; then
    echo "$benchmark,$backend,,missing"
    return
  fi

  start=$(perl -MTime::HiRes=time -e 'printf "%.3f", time')
  out=$(timeout "$TIMEOUT" \
    "$EBMC" \
    "$file" \
    --new-ic3 \
    --new-ic3-sat-solver \
    "$backend" \
    2>&1) || status=$?
  status=${status:-0}
  end=$(perl -MTime::HiRes=time -e 'printf "%.3f", time')
  t=$(echo "$end $start" | awk '{printf "%.2f", $1-$2}')

  if [ "$status" = 124 ] || [ "$status" = 142 ]; then
    res=timeout
    t=""
  elif echo "$out" | grep -q "PROVED"; then
    res=proved
  elif echo "$out" | grep -q "REFUTED"; then
    res=refuted
  else
    res="error"
    t=""
  fi

  echo "$benchmark,$backend,$t,$res"
}

if [ "$#" -gt 0 ]; then
  for b in "$@"; do
    for backend in $BACKENDS; do
      run_one "$b" "$backend"
    done
  done | sort -t, -k1,1 -k2,2
else
  tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/new-ic3-sat.XXXXXX")
  trap 'rm -rf "$tmpdir"' EXIT INT TERM

  (
    for path in "$BENCH_DIR"/*.aig; do
      [ -e "$path" ] || continue
      benchmark=$(basename "$path" .aig)
      for backend in $BACKENDS; do
        printf '%s,%s\n' "$benchmark" "$backend"
      done
    done
  ) | xargs -P "$JOBS" -I '{}' sh -c '
        pair=$1
        benchmark=${pair%,*}
        backend=${pair#*,}
        bench_dir=$2
        ebmc=$3
        timeout_s=$4
        tmpdir=$5
        file=$bench_dir/$benchmark.aig
        outfile=$tmpdir/$benchmark.$backend.csv

        if [ ! -e "$file" ]; then
          echo "$benchmark,$backend,,missing" > "$outfile"
          exit 0
        fi

        start=$(perl -MTime::HiRes=time -e "printf \"%.3f\", time")
        out=$(timeout "$timeout_s" \
          "$ebmc" \
          "$file" \
          --new-ic3 \
          --new-ic3-sat-solver \
          "$backend" \
          2>&1) || status=$?
        status=${status:-0}
        end=$(perl -MTime::HiRes=time -e "printf \"%.3f\", time")
        t=$(echo "$end $start" | awk "{printf \"%.2f\", \$1-\$2}")

        if [ "$status" = 124 ] || [ "$status" = 142 ]; then
          res=timeout
          t=""
        elif echo "$out" | grep -q "PROVED"; then
          res=proved
        elif echo "$out" | grep -q "REFUTED"; then
          res=refuted
        else
          res=error
          t=""
        fi

        echo "$benchmark,$backend,$t,$res" > "$outfile"
      ' sh '{}' "$BENCH_DIR" "$EBMC" "$TIMEOUT" "$tmpdir"

  cat "$tmpdir"/*.csv | sort -t, -k1,1 -k2,2
fi
