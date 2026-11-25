#!/bin/sh

BASE=$(dirname $0)

if ! which ebmc 2>/dev/null 1>&2 ; then
  echo "ebmc binary not found in PATH"
  exit 1
fi

VERILOG_FILES=$@

cleanup()
{
  rm -rf "$vcd_dir"
}
vcd_dir=$(mktemp -d vcd.XXXXX)
trap cleanup EXIT

ebmc $VERILOG_FILES --random-traces --random-seed 0 \
  --trace-steps 100 --number-of-traces 20 \
  --vcd $vcd_dir/trace.vcd

# pyvcd does not support indexed names as arise from generate statements
perl -p -i -e 's/\[(\d+)\]/__$1__/g' $vcd_dir/trace.vcd*

## If we were to use --neural-engine:
## python3 $BASE/nuterm/nuterm.py \
##   --strategy anticorr_sumofrelu2 \
##   $BASE/../../bla.vcd.* | \
##   tail -n 1 | cut -f2 -d: | \
##   sed 's/main\.//g' | sed 's/^/Candidate: /'
## echo

python3 $BASE/nuterm/nuterm.py \
  --strategy anticorr_sumoflinears_or_concat \
  --vcd-prefix $vcd_dir/trace.vcd \
  --seed 0 \
  $VERILOG_FILES
