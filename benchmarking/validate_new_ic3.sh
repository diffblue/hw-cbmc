#!/bin/sh
# Validate --new-ic3 verdicts against expected results in hwmcc08results.csv
# (column 3, abc's verdict: "uns" = proved, "sat" = refuted).
# Usage: validate_new_ic3.sh <timeout-seconds> <benchmark>...
EBMC=${EBMC:-../src/ebmc/ebmc}
TIMEOUT=$1
shift
mismatches=0
for b in "$@"; do
  f=hwmcc08public-smv/$b.smv
  [ -e "$f" ] || continue
  expected=`grep "^\"$b\"," hwmcc08results.csv | cut -d ',' -f 3 | tr -d '"'`
  [ "$expected" = uns ] || [ "$expected" = sat ] || continue
  out=`perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT $EBMC "$f" --new-ic3 2>&1`
  if echo "$out" | grep -q "PROVED"; then got=uns
  elif echo "$out" | grep -q "REFUTED"; then got=sat
  else got=timeout
  fi
  if [ "$got" = timeout ]; then
    echo "$b: timeout (expected $expected)"
  elif [ "$got" != "$expected" ]; then
    echo "$b: MISMATCH got $got expected $expected"
    mismatches=$((mismatches+1))
  else
    echo "$b: ok ($got)"
  fi
done
echo "mismatches: $mismatches"
