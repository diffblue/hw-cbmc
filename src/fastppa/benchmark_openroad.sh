#!/bin/bash
# Compare fastppa estimates against OpenROAD (Yosys+ABC+NanGate45).
# Requires: Docker with openroad/orfs image.
# Usage: ./benchmark_openroad.sh [design.sv top_module]

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
FASTPPA=${SCRIPT_DIR}/fastppa
REG=${SCRIPT_DIR}/../../regression/fastppa

if [ ! -x "$FASTPPA" ]; then
  echo "Error: fastppa binary not found. Run 'make -C src fastppa' first."
  exit 1
fi

DESIGNS="${1:-}"
if [ -z "$DESIGNS" ]; then
  DESIGNS="
    $REG/blocks/adder.sv:adder
    $REG/blocks/multiplier.sv:multiplier
    $REG/blocks/shifter.sv:shifter
    $REG/designs/alu.sv:alu
    $REG/designs/fir4.sv:fir4
    $REG/designs/pipe_mult.sv:pipe_mult
    $REG/designs/riscv_pipe.sv:riscv_pipe
  "
fi

printf "%-16s %10s %10s %8s %8s\n" "Design" "fastppa" "OpenROAD" "Ratio" "Delay"
printf "%-16s %10s %10s %8s %8s\n" "--------" "--------" "--------" "------" "------"

for d in $DESIGNS; do
  file=${d%%:*}; top=${d##*:}
  [ -f "$file" ] || continue

  # fastppa
  out=$($FASTPPA "$file" --top "$top" --process 45nm 2>&1)
  rt_area=$(echo "$out" | grep "^  Total:" | head -1 | awk '{print $2}')
  rt_delay=$(echo "$out" | grep "Reg-to-reg" | sed 's/.*(\(.*\) ns)/\1/')

  # OpenROAD via Docker
  or_area=$(docker run --rm --platform linux/amd64 \
    -v "$(dirname "$file"):/d" openroad/orfs:latest bash -c "
    export PATH=/OpenROAD-flow-scripts/tools/install/yosys/bin:\$PATH
    LIB=/OpenROAD-flow-scripts/flow/platforms/nangate45/lib/NangateOpenCellLibrary_typical.lib
    yosys -p \"read_verilog -sv /d/$(basename "$file"); synth -top $top -flatten; dfflibmap -liberty \$LIB; abc -liberty \$LIB; stat -liberty \$LIB\" 2>&1 | grep 'Chip area' | awk '{print \$NF}'
  " 2>/dev/null)

  if [ -n "$or_area" ] && [ -n "$rt_area" ]; then
    ratio=$(echo "scale=2; $rt_area / $or_area" | bc 2>/dev/null)
    printf "%-16s %10s %10s %8sx %7sns\n" "$top" "$rt_area" "$or_area" "$ratio" "$rt_delay"
  else
    printf "%-16s %10s %10s %8s %8s\n" "$top" "${rt_area:-ERR}" "${or_area:-ERR}" "-" "-"
  fi
done
