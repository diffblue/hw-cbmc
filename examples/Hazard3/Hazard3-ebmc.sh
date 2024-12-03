#!/bin/sh

# abort on error
set -e

# clone Hazard3 repo if not done yet
if [ ! -e Hazard3/.git ] ; then
  git clone https://github.com/Wren6991/Hazard3 --branch v1.0 --depth 1
fi

cd Hazard3

ebmc -I hdl \
  -D HAZARD3_ASSERTIONS --bound 0 --top hazard3_alu \
  hdl/arith/hazard3_alu.v \
  hdl/arith/hazard3_priority_encode.v \
  hdl/arith/hazard3_onehot_encode.v \
  hdl/arith/hazard3_onehot_priority.v \
  hdl/arith/hazard3_shift_barrel.v

# expected elaboration-time constant, but got `hazard3_muldiv_seq.properties.i'
# $past, for loop,
# covered by regression/verilog/system-functions/past3.desc
# ebmc -I hdl -D HAZARD3_ASSERTIONS --systemverilog --bound 0 hdl/arith/hazard3_muldiv_seq.v

ebmc -I hdl \
  -D HAZARD3_ASSERTIONS --bound 0 \
  hdl/arith/hazard3_shift_barrel.v

# conflicting assignment types,
# covered by KNOWNBUG regression/verilog/synthesis/synthesis3.desc
if false ; then
ebmc -I hdl -I test/formal/riscv-formal/tb -I test/formal/instruction_fetch_match \
  -D HAZARD3_ASSERTIONS --systemverilog --bound 0 --top hazard3_core \
  hdl/hazard3_core.v \
  hdl/arith/hazard3_alu.v \
  hdl/arith/hazard3_priority_encode.v \
  hdl/arith/hazard3_onehot_priority.v \
  hdl/arith/hazard3_onehot_priority_dynamic.v \
  hdl/arith/hazard3_onehot_encode.v \
  hdl/arith/hazard3_shift_barrel.v \
  hdl/arith/hazard3_branchcmp.v \
  hdl/hazard3_csr.v \
  hdl/hazard3_irq_ctrl.v \
  hdl/hazard3_decode.v \
  hdl/hazard3_instr_decompress.v \
  hdl/hazard3_frontend.v
fi

# conflicting assignment types,
# covered by KNOWNBUG regression/verilog/synthesis/synthesis3.desc
if false ; then
ebmc -I hdl -I test/formal/riscv-formal/tb -I test/formal/instruction_fetch_match \
  -D HAZARD3_ASSERTIONS --systemverilog --bound 0 \
  hdl/hazard3_cpu_2port.v \
  hdl/hazard3_core.v \
  hdl/arith/hazard3_alu.v \
  hdl/arith/hazard3_branchcmp.v \
  hdl/arith/hazard3_priority_encode.v \
  hdl/arith/hazard3_onehot_encode.v \
  hdl/arith/hazard3_onehot_priority.v \
  hdl/arith/hazard3_onehot_priority_dynamic.v \
  hdl/arith/hazard3_shift_barrel.v \
  hdl/hazard3_csr.v \
  hdl/hazard3_irq_ctrl.v \
  hdl/hazard3_decode.v \
  hdl/hazard3_instr_decompress.v \
  hdl/hazard3_frontend.v
fi

# four properties fail
if false ; then
ebmc -I hdl -D HAZARD3_ASSERTIONS --systemverilog --bound 0 --top hazard3_csr \
  hdl/hazard3_csr.v \
  hdl/hazard3_irq_ctrl.v \
  hdl/arith/hazard3_onehot_encode.v \
  hdl/arith/hazard3_onehot_priority.v \
  hdl/arith/hazard3_onehot_priority_dynamic.v
fi

ebmc -I hdl \
  -D HAZARD3_ASSERTIONS --bound 0 --top hazard3_decode \
  hdl/hazard3_decode.v \
  hdl/hazard3_instr_decompress.v

# conflicting assignment types,
# covered by KNOWNBUG regression/verilog/synthesis/synthesis3.desc
# ebmc -I hdl -D HAZARD3_ASSERTIONS --systemverilog --bound 0 hdl/hazard3_frontend.v

# property disabled by config
# ebmc -I hdl -D HAZARD3_ASSERTIONS --bound 0 hdl/hazard3_instr_decompress.v

# property fails
if false ; then
ebmc -I hdl \
  -D HAZARD3_ASSERTIONS --bound 0 \
  hdl/hazard3_power_ctrl.v
fi
