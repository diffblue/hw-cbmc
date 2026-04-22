#!/bin/sh
# Compare old --ic3 vs new --new-ic3 on hwmcc08public-smv benchmarks.
# Usage: compare_ic3.sh <timeout-seconds> <benchmark>...
EBMC=${EBMC:-../src/ebmc/ebmc}
TIMEOUT=$1
shift
printf "%-28s %10s %10s %8s %8s\n" benchmark old new old_res new_res
for b in "$@"; do
  f=hwmcc08public-smv/$b.smv
  [ -e "$f" ] || { echo "$b: missing"; continue; }
  for engine in ic3 new-ic3; do
    start=`perl -MTime::HiRes=time -e 'printf "%.3f", time'`
    out=`perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $EBMC "$f" --$engine 2>&1`
    status=$?
    end=`perl -MTime::HiRes=time -e 'printf "%.3f", time'`
    t=`echo "$end $start" | awk '{printf "%.2f", $1-$2}'`
    if [ $status = 124 ] || [ $status = 142 ]; then res=TIMEOUT; t="-"
    elif echo "$out" | grep -q "PROVED"; then res=proved
    elif echo "$out" | grep -q "REFUTED"; then res=refuted
    else res="err($status)"
    fi
    if [ "$engine" = ic3 ]; then old_t=$t; old_r=$res; else new_t=$t; new_r=$res; fi
  done
  printf "%-28s %10s %10s %8s %8s\n" "$b" "$old_t" "$new_t" "$old_r" "$new_r"
done
