#!/bin/bash
# Ground truth G1 for one design (see PROTOCOL.md). Runs inside the
# openroad/orfs image. Prints one tab-separated line:
#   name status area_um2 delay_ns clock_ports seconds
#   clock_energy_fJ data_energy_fJ leakage_uW
# The energies are per clock cycle: clock_energy with all inputs constant,
# and data_energy per unit of input activity (toggles per cycle).
#
# Usage: [PLATFORM=<name>] gt_flow.sh <workdir> <name> <top> <sources>
#          <incdirs> <defines>
# (lists are space-separated; platforms are defined in platforms.sh)

set -u
work=$1; name=$2; top=$3; sources=$4; incdirs=$5; defines=$6

ORFS=/OpenROAD-flow-scripts
YOSYS=$ORFS/tools/install/yosys/bin/yosys
OPENROAD=$ORFS/tools/install/OpenROAD/bin/openroad
TIMEOUT=${GT_TIMEOUT:-600}
here=$(cd "$(dirname "$0")" && pwd)
. "$here/platforms.sh"

dir=$work/$(echo "$name" | tr '/' '_')
mkdir -p "$dir"
start=$(date +%s)

# Uncompressed copies of the liberty files, shared by all designs.
libdir=$work/.lib
mkdir -p "$libdir"
liberty=""
for l in $LIBS; do
  f=$libdir/$(basename "$l" .gz)
  [ -f "$f" ] || { zcat -f "$l" > "$f.$$" && mv "$f.$$" "$f"; }
  liberty="$liberty -liberty $f"
done
dont_use=""
for c in $DONT_USE; do dont_use="$dont_use -dont_use $c"; done

flags=""
for i in $incdirs; do flags="$flags -I$i"; done
for d in $defines; do flags="$flags -D$d"; done

cat > "$dir/synth.ys" <<EOF
read_verilog -sv -defer $flags $sources
hierarchy -top $top
synth -top $top -flatten
dfflibmap $liberty $dont_use
abc $liberty $dont_use
opt_clean
stat $liberty
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
$(for l in $LEFS; do echo "read_lef $l"; done)
$(for l in $liberty; do [ "$l" = -liberty ] || echo "read_liberty $l"; done)
read_verilog $dir/net.v
link_design $top
# Liberty files differ in their units; use ns and W throughout.
set_cmd_units -time ns -power W -capacitance pF
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
# Power per cycle of the 50 ns clock: first with constant inputs, which
# leaves the clock, then with an input activity of 0.1.
set_power_activity -input -activity 0
report_power -digits 8 > $dir/power0.rpt
set_power_activity -input -activity 0.1
report_power -digits 8 > $dir/power1.rpt
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
# report_power: the 'Total' row has internal, switching, leakage and total
# power, in W.
total() { awk '$1 == "Total" { print $2 + $3, $4; exit }' "$1"; }
read -r dyn0 leak < <(total "$dir/power0.rpt")
read -r dyn1 _ < <(total "$dir/power1.rpt")
energy=$(awk -v d0="${dyn0:-0}" -v d1="${dyn1:-0}" -v l="${leak:-0}" \
  'BEGIN { p = 50e-9; printf "%.6g\t%.6g\t%.6g", d0 * p * 1e15,
           (d1 - d0) * p * 1e15 / 0.1, l * 1e6 }')
printf '%s\tok\t%s\t%s\t%s\t%s\t%s\n' "$name" "$area" "${delay:-0}" \
  "${clocks:-none}" $(( $(date +%s) - start )) "$energy"
