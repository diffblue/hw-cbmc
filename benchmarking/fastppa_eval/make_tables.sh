#!/bin/sh
# Regenerate the cost tables compiled into fastppa.
# Usage: make_tables.sh <C/params.tsv> <dir with gt_C_<platform>.tsv>
set -eu
here=$(cd "$(dirname "$0")" && pwd)
src=$here/../../src/fastppa
params=$1; gt=$2
for p in nangate45 sky130hd gf180 ihp-sg13g2 asap7 gt2n; do
  "$here/fit.py" "$params" "$gt/gt_C_$p.tsv" \
    "$src/cost_table_$(echo $p | tr - _).inc" "$here/results/fit_$p.txt" \
    > /dev/null
done
for n in 90nm 65nm 28nm 14nm; do
  "$here/derive.py" "$src/cost_table_nangate45.inc" $n "$src/cost_table_$n.inc"
done
for n in 5nm 3nm; do
  "$here/derive.py" "$src/cost_table_asap7.inc" $n "$src/cost_table_$n.inc"
done
