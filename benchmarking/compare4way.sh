#!/bin/sh
# 4-way comparison: ebmc --ic3, ebmc --new-ic3, rIC3, pono
# on HWMCC08 benchmarks (SMV translations for ebmc/pono, AIGER for rIC3).
#
# Usage: compare4way.sh <timeout-seconds> <benchmark>...
# Output: CSV lines  benchmark,tool,seconds,result
#
# Environment:
#   EBMC          path to ebmc         (default: ../src/ebmc/ebmc)
#   RIC3          path to rIC3        (default: ric3 in PATH)
#   PONO          path to pono        (default: pono in PATH)
#   PONO_SMV_DIR  directory with INVARSPEC-converted SMV files; pono does
#                 not parse "SPEC AG p". Convert with:
#                 sed 's/^SPEC AG \(.*\) --.*$/INVARSPEC \1;/'
EBMC=${EBMC:-../src/ebmc/ebmc}
RIC3=${RIC3:-ric3}
PONO=${PONO:-pono}
PONO_SMV_DIR=${PONO_SMV_DIR:-/tmp/pono-smv}
TIMEOUT=$1
shift

run_one() {
  # $1 = tool name, rest = command
  tool=$1; shift
  start=`perl -MTime::HiRes=time -e 'printf "%.3f", time'`
  out=`perl -e 'alarm shift @ARGV; exec @ARGV' $TIMEOUT "$@" 2>&1`
  status=$?
  end=`perl -MTime::HiRes=time -e 'printf "%.3f", time'`
  t=`echo "$end $start" | awk '{printf "%.2f", $1-$2}'`
  case $tool in
    ebmc-*)
      if [ $status = 142 ]; then res=timeout; t=""
      elif echo "$out" | grep -q "PROVED"; then res=proved
      elif echo "$out" | grep -q "REFUTED"; then res=refuted
      else res="error"; t=""
      fi;;
    ric3)
      # rIC3: prints UNSAT (safe) / SAT (unsafe)
      if [ $status = 142 ]; then res=timeout; t=""
      elif echo "$out" | grep -qx "UNSAT"; then res=proved
      elif echo "$out" | grep -qx "SAT"; then res=refuted
      else res="error"; t=""
      fi;;
    pono)
      # pono: prints unsat (safe) / sat (unsafe)
      if [ $status = 142 ]; then res=timeout; t=""
      elif echo "$out" | grep -q "^unsat"; then res=proved
      elif echo "$out" | grep -q "^sat"; then res=refuted
      else res="unknown"; t=""
      fi;;
  esac
  echo "$b,$tool,$t,$res"
}

for b in "$@"; do
  smv=hwmcc08public-smv/$b.smv
  aig=hwmcc08/$b.aig
  [ -e "$smv" ] || { echo "$b,,,missing"; continue; }
  run_one ebmc-ic3 $EBMC "$smv" --ic3
  run_one ebmc-new-ic3 $EBMC "$smv" --new-ic3
  [ -e "$aig" ] && command -v "$RIC3" >/dev/null 2>&1 && \
    run_one ric3 $RIC3 check "$aig" ic3
  # pono needs INVARSPEC instead of SPEC AG (converted copies)
  command -v "$PONO" >/dev/null 2>&1 && [ -e "$PONO_SMV_DIR/$b.smv" ] && \
    run_one pono $PONO -e ic3bits -k 10000 "$PONO_SMV_DIR/$b.smv"
done
