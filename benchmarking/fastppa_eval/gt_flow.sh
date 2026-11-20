#!/bin/bash
# Ground truth G1 for one design (see PROTOCOL.md). Runs inside the
# openroad/orfs image. Prints one tab-separated line:
#   name  status  area_um2  delay_ns  clock_ports  seconds
#
# Usage: gt_flow.sh <workdir> <name> <top> <sources> <incdirs> <defines>
# (lists are space-separated)

set -u
work=$1; name=$2; top=$3; sources=$4; incdirs=$5; defines=$6

ORFS=/OpenROAD-flow-scripts
YOSYS=$ORFS/tools/install/yosys/bin/yosys
OPENROAD=$ORFS/tools/install/OpenROAD/bin/openroad
LIB=$ORFS/flow/platforms/nangate45/lib/NangateOpenCellLibrary_typical.lib
LEF=$ORFS/flow/platforms/nangate45/lef
TIMEOUT=${GT_TIMEOUT:-600}

dir=$work/$(echo "$name" | tr '/' '_')
mkdir -p "$dir"
start=$(date +%s)

flags=""
for i in $incdirs; do flags="$flags -I$i"; done
for d in $defines; do flags="$flags -D$d"; done

cat > "$dir/synth.ys" <<EOF
read_verilog -sv -defer $flags $sources
hierarchy -top $top
synth -top $top -flatten
dfflibmap -liberty $LIB
abc -liberty $LIB
opt_clean
stat -liberty $LIB
write_verilog -noattr $dir/net.v
EOF

# ABC occasionally fails transiently under parallel load; retry once.
if ! timeout "$TIMEOUT" "$YOSYS" -q -l "$dir/synth.log" "$dir/synth.ys" \
     > /dev/null 2>&1 &&
   ! timeout "$TIMEOUT" "$YOSYS" -q -l "$dir/synth.log" "$dir/synth.ys" \
     > /dev/null 2>&1; then
  printf '%s\tsynth_failed\t\t\t\t%s\n' "$name" $(( $(date +%s) - start ))
  exit 0
fi

area=$(grep -E 'Chip area for (top )?module' "$dir/synth.log" | tail -1 \
       | awk '{print $NF}')

cat > "$dir/sta.tcl" <<EOF
read_lef $LEF/NangateOpenCellLibrary.tech.lef
read_lef $LEF/NangateOpenCellLibrary.macro.lef
read_liberty $LIB
read_verilog $dir/net.v
link_design $top
set ports {}
foreach p [all_registers -clock_pins] {
  set net [get_nets -quiet -of_objects \$p]
  if {\$net == ""} continue
  set pt [get_ports -quiet [get_full_name \$net]]
  if {\$pt != ""} { lappend ports [get_full_name \$pt] }
}
set ports [lsort -unique \$ports]
puts "CLOCK_PORTS: \$ports"
if {[llength \$ports]} {
  create_clock -name c -period 50 [get_ports \$ports]
} else {
  create_clock -name c -period 50
}
set ins {}
foreach p [all_inputs] {
  if {[lsearch -exact \$ports [get_full_name \$p]] < 0} { lappend ins \$p }
}
if {[llength \$ins]} { set_input_delay 0 -clock c \$ins }
if {[llength [all_outputs]]} { set_output_delay 0 -clock c [all_outputs] }
report_checks -path_delay max -digits 4
exit
EOF

if ! timeout "$TIMEOUT" "$OPENROAD" -no_init -exit "$dir/sta.tcl" \
     > "$dir/sta.log" 2>&1; then
  printf '%s\tsta_failed\t%s\t\t\t%s\n' "$name" "$area" \
    $(( $(date +%s) - start ))
  exit 0
fi

# The worst data arrival time over all path groups; report_checks lists
# one path per group (e.g. register-to-register and reset recovery), and
# each path's arrival time appears twice.
delay=$(grep 'data arrival time' "$dir/sta.log" | awk '{print $1}' \
        | sort -g | tail -1)
clocks=$(grep '^CLOCK_PORTS:' "$dir/sta.log" | sed 's/^CLOCK_PORTS: *//' \
         | tr ' ' ',')
printf '%s\tok\t%s\t%s\t%s\t%s\n' "$name" "$area" "${delay:-0}" \
  "${clocks:-none}" $(( $(date +%s) - start ))
