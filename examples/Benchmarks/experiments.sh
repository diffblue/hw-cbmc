#!/bin/bash

for BM in *.sv
do
  TOP=$(grep -w module $BM | awk '{print $2}' | sed 's/(.*//')
  echo "BENCHMARK: $BM ($TOP)"
  cat > $BM.jg.tcl << EOF
clear -all
analyze -sv12 $BM
elaborate -top $TOP
clock clk
reset -none
prove -bg -all
exit
EOF
  /usr/bin/time -v timeout --kill-after=600s 3600s jg -allow_unsupported_OS -no_gui -acquire_proj -fpv $BM.jg.tcl
done

for BM in *.sv
do
  TOP=$(grep -w module $BM | awk '{print $2}' | sed 's/(.*//')
  echo "BENCHMARK: $BM ($TOP)"
  cat > $BM.vcf.tcl << EOF
set CPU_per_lic 12
set lic_number 1
read_file -format sverilog -sva -top $TOP $BM
create_clock clk -period 100
check_fv
EOF
  /usr/bin/time -v timeout --kill-after=600s 3600s vcf -no_ui -file $BM.vcf.tcl
done
