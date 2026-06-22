Rocket Core: Real-World fastppa Validation
===========================================

`rocket_full.v` is the `Rocket` RV32 in-order pipeline core module (RISC-V
Rocket Chip, TinyRocket chipyard config) plus its 7 dependencies
(`plusarg_reader`, `RVCExpander`, `IBuf`, `CSRFile`, `BreakpointUnit`,
`ALU`, `MulDiv`, `PlusArgTimeout`), extracted from the flattened FIRRTL
Verilog output `chipyard.TestHarness.TinyRocketConfig.top.v` published by
[RTL-Timer](https://github.com/hkust-zhiyao/RTL-Timer) (BSD-3-Clause,
Copyright (c) 2024 Wenji Fang). That repository also publishes a real
Synopsys PrimeTime post-route timing/power/area report for this exact
module at NanGate45
(`report_example/rpt_data/net/Rocket_TinyRocket_route_TYP_SAIF_SDF/`),
which is what this benchmark is calibrated/checked against. `Rocket` and
its submodules ultimately originate from the BSD/Apache-2.0-licensed
[rocket-chip](https://github.com/chipsalliance/rocket-chip) /
[chipyard](https://github.com/ucb-bar/chipyard) projects.

Why this design: unlike the small, hand-written designs in
`regression/fastppa/`, this is a real, deep (39 levels of logic per
PrimeTime), multi-thousand-line RISC-V core with genuine commercial EDA
ground truth, letting `fastppa`'s estimates be checked against more than
just an open-source synthesis proxy. See
`src/fastppa/DOCKER_VALIDATION.md` ("Real-world validation: Rocket core")
for the full comparison.

Usage
-----

    $ fastppa rocket_full.v --top Rocket --process 45nm

PrimeTime ground truth
----------------------

The `primetime/` subdirectory contains unmodified, checksum-verified
copies of the PrimeTime report files (see `primetime/NOTICE` for the
license and `primetime/fetch_reports.sh` to re-verify them against the
pinned upstream commit). Headline numbers, as parsed from those reports:

- Total cell area: 42014.97 um2 (`Rocket.total_area.rpt`)
- Critical path (`CLK_clock`, max_delay/setup): 2.989 ns, 39 levels of
  logic (`Rocket.qor.rpt`)
- Per-module cell area and power: `Rocket.hier_cell_area.txt`

`compare_primetime.py` parses these reports, runs fastppa on the whole
core and on each hierarchical submodule, and prints the comparison
tables shown in `src/fastppa/COMPARISON.md`.

(`fastppa`'s own delay number is closer to what a single-pass open-source
synthesis flow, Yosys+ABC+OpenSTA, produces on the same RTL than to this
post-route, timing-closed PrimeTime number -- see DOCKER_VALIDATION.md for
why.)
