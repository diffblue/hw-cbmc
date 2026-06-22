Benchmarks for fastppa Validation
===================================

This file lists open-source benchmark suites suitable for validating fastppa
estimates against published or reproducible synthesis results.

Primary Validation Set
----------------------

### MetRex (25,868 designs, NanGate 45nm)

- URL: https://github.com/scale-lab/MetRex
- Dataset: https://huggingface.co/datasets/scale-lab/MetRex
- Paper: arXiv:2411.03471 (ASP-DAC 2025)
- Contents: Verilog designs with post-synthesis area, delay, and static power
  (Yosys + OpenSTA, NanGate 45nm open PDK).
- Use: large-scale statistical validation of estimation accuracy.

### MasterRTL (90 designs, Synopsys DC, NanGate 45nm)

- URL: https://github.com/hkust-zhiyao/MasterRTL
- Paper: arXiv:2311.08441 (ICCAD 2023)
- Contents: 90 RTL designs (ISCAS'89, ITC'99, OpenCores, VexRiscv, NVDLA,
  Rocket/BOOM) synthesized with Synopsys Design Compiler 2021. Reports TNS,
  WNS, total power, and gate area.
- Use: gold-standard commercial synthesis ground truth for calibration.

Scaling Validation
------------------

### EPFL Combinational Benchmarks

- URL: https://github.com/lsils/benchmarks
- Contents: 23 circuits including arithmetic (multiplier, divider, sqrt,
  log2, adder) at multiple bit-widths (32/64/128). Available in Verilog.
- Use: validate that area/delay scales correctly with bit-width.

### VexRiscv (26 configurations, 7K–530K gates)

- URL: https://github.com/SpinalHDL/VexRiscv
- Contents: parameterizable RISC-V CPU with 26 configurations varying
  pipeline depth, cache size, multiplier type, branch prediction.
- Use: validate sensitivity to architectural parameters.

Multi-Node Validation
---------------------

### OpenROAD Flow Scripts (ASAP7, NanGate45, SKY130)

- URL: https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts
- Contents: RTL-to-GDS flow for designs (GCD, Ibex, AES, JPEG, SweRV)
  targeting ASAP7 (7nm predictive), NanGate45, and SKY130HD (130nm-class).
- Use: generate reference PPA at multiple process nodes for cross-node
  scaling validation.

Real-World Designs
------------------

### ISPRAS HDL Benchmarks (IWLS'05 / OpenCores)

- URL: https://github.com/ispras/hdl-benchmarks
- Contents: curated Verilog RTL collection including FPU, Ethernet, USB,
  DES, AES, and RISC cores (2K–672K gates).
- Use: realistic diversity of design styles and sizes.

### MIT CEP (Common Evaluation Platform)

- URL: https://github.com/mit-ll/CEP
- Contents: SoC with accelerator cores (AES, DES3, SHA256, MD5, GPS,
  DFT/IDFT, FIR, IIR) on Chipyard/RISC-V.
- Use: parameterizable accelerators for DSP/crypto estimation testing.

### Chipyard / Rocket / BOOM

- URL: https://github.com/ucb-bar/chipyard
- Contents: RISC-V cores with parameterizable width (32/64-bit), issue
  width, cache sizes. 18 configurations available in MasterRTL dataset.
- Use: processor cores with known architectural parameters and published
  synthesis numbers.

Validation Strategy
-------------------

1. Calibrate on MasterRTL (commercial DC ground truth, 45nm).
2. Validate operator scaling with EPFL arithmetic benchmarks.
3. Statistical validation with MetRex (25K+ designs).
4. Cross-node validation with OpenROAD (7nm, 45nm, 130nm).
5. Real-world complexity with IWLS/CEP/Chipyard.
