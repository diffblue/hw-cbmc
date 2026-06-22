#!/bin/bash
# Validate operator cost scaling across bit-widths.
# Generates parameterized designs and compares fastppa vs Yosys.
# Requires: Docker with hdlc/ghdl:yosys image.

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
FASTPPA=${SCRIPT_DIR}/fastppa
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

if [ ! -x "$FASTPPA" ]; then
  echo "Error: fastppa binary not found."
  exit 1
fi

# Generate designs
for w in 8 16 32 64 128; do
  echo "module adder_${w}(input clk, input [${w}-1:0] a, b, output reg [${w}-1:0] sum);
  always @(posedge clk) sum <= a + b;
endmodule" > $TMPDIR/adder_${w}.sv
done

for w in 8 16 32 64; do
  echo "module mult_${w}(input clk, input [${w}-1:0] a, b, output reg [$((w*2-1)):0] p);
  always @(posedge clk) p <= a * b;
endmodule" > $TMPDIR/mult_${w}.sv
done

printf "%-12s %8s %8s %6s\n" "Design" "fastppa" "Yosys" "Ratio"
printf "%-12s %8s %8s %6s\n" "--------" "------" "-----" "-----"

for f in $TMPDIR/*.sv; do
  top=$(basename $f .sv)

  # fastppa
  rt=$($FASTPPA "$f" --top "$top" --process 45nm 2>&1 | grep "Comb. area:" | awk '{print $3}')

  # Yosys (logic cells × 1.5 µm²)
  yosys_cells=$(docker run --rm --platform linux/amd64 \
    -v "$TMPDIR:/w" hdlc/ghdl:yosys \
    yosys -p "read_verilog -sv /w/$(basename $f); synth -top $top -flatten; stat" 2>/dev/null \
    | grep "Number of cells:" | tail -1 | awk '{print $NF}')

  if [ -n "$yosys_cells" ] && [ "$yosys_cells" -gt 0 ] && [ -n "$rt" ]; then
    # Subtract DFFs for comb-only comparison
    dffs=$(docker run --rm --platform linux/amd64 \
      -v "$TMPDIR:/w" hdlc/ghdl:yosys \
      yosys -p "read_verilog -sv /w/$(basename $f); synth -top $top -flatten; stat" 2>/dev/null \
      | grep -E "_DFF_|_SDFF" | awk '{sum+=$NF} END {print sum+0}')
    logic=$((yosys_cells - dffs))
    yosys_area=$(echo "$logic * 1.5" | bc)
    ratio=$(echo "scale=2; $rt / $yosys_area" | bc 2>/dev/null)
    printf "%-12s %8s %8s %6sx\n" "$top" "$rt" "$yosys_area" "$ratio"
  fi
done
