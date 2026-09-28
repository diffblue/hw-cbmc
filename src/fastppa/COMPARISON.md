fastppa vs Synopsys PrimeTime (Rocket core)
===========================================

This file compares fastppa against a genuine Synopsys PrimeTime
post-route report for a real RISC-V core. Every number below is
produced by a checked-in script from checked-in, checksum-verified
input data — nothing in this file is hand-transcribed.

(An earlier revision of this file cited PrimeTime module delays and
speed benchmarks that no script or artifact could reproduce; it was
deleted and survives only in git history. The per-module area and power
values it quoted did turn out to correspond to real report rows, which
are now properly sourced below.)

Ground truth
------------

The [RTL-Timer](https://github.com/hkust-zhiyao/RTL-Timer) project
(BSD-3-Clause, Copyright (c) 2024 Wenji Fang) publishes a real
PrimeTime T-2022.03-SP3 post-route report set for the `Rocket` RV32
core (TinyRocket chipyard config) at NanGate45, with SAIF-based
switching activity:

- repository commit: `206ff4078368c251d2fafaffcc648282c68316f1`
- directory: `report_example/rpt_data/net/Rocket_TinyRocket_route_TYP_SAIF_SDF/`

The relevant report files are checked into
`benchmarking/rocket_core/primetime/` as unmodified byte-for-byte
copies (`SHA256SUMS` records their checksums; `NOTICE` records the
license). `fetch_reports.sh` in that directory re-downloads them from
the pinned commit and verifies both the checksums and the checked-in
copies, so the ground truth can be re-audited against upstream at any
time. The per-module areas come from the hierarchical-cell rows of
`Rocket.cell_pwr_area.rpt` (1 MB, not checked in; `fetch_reports.sh`
regenerates the checked-in 7-line extract `Rocket.hier_cell_area.txt`
from it and verifies its checksum too).

The RTL fastppa runs on (`benchmarking/rocket_core/rocket_full.v`) is
the `Rocket` module and its submodules extracted from the same
project's `chipyard.TestHarness.TinyRocketConfig.top.v` — the same
design the PrimeTime reports describe.

Method
------

All comparisons are produced by
`benchmarking/rocket_core/compare_primetime.py`, which:

- parses total cell area from `Rocket.total_area.rpt`,
- parses the critical path (`CLK_clock` max_delay/setup group: 2.989 ns,
  39 levels of logic) from `Rocket.qor.rpt`,
- parses per-module cell area and power from `Rocket.hier_cell_area.txt`
  (the hierarchical-cell rows of the per-cell power/area report) and
  total power from `Rocket.report_power.rpt`,
- runs `fastppa benchmarking/rocket_core/rocket_full.v --top <module>
  --process 45nm` for the whole core and for each of the five
  hierarchical submodules, and
- prints the tables below.

To reproduce:

    $ make -C src/fastppa
    $ benchmarking/rocket_core/primetime/fetch_reports.sh   # optional audit
    $ benchmarking/rocket_core/compare_primetime.py

Results
-------

Core (whole design, `--top Rocket`)

| quantity | PrimeTime (post-route) | fastppa | ratio |
|----------|-----------------------|---------|-------|
| cell area (µm²) | 42014.97 | 56499.5 | 1.34 |
| critical path (ns) | 2.989 (39 levels of logic) | 5.825 | 1.95 |

Per-module cell area

| instance | module | PrimeTime (µm²) | fastppa (µm²) | ratio |
|----------|--------|-----------------|---------------|-------|
| csr | CSRFile | 8968.0 | 17004.8 | 1.90 |
| div | MulDiv | 5734.0 | 4974.4 | 0.87 |
| ibuf | IBuf | 2998.0 | 6944.3 | 2.32 |
| alu | ALU | 2100.0 | 2853.0 | 1.36 |
| bpu | BreakpointUnit | 496.9 | 814.1 | 1.64 |

Per-module power share (of the five-module subtotal)

| instance | module | PrimeTime (mW) | PT share | fastppa (mW) | fastppa share |
|----------|--------|----------------|----------|--------------|---------------|
| csr | CSRFile | 24.40 | 31.8% | 645.7 | 48.9% |
| div | MulDiv | 30.60 | 39.9% | 429.1 | 32.5% |
| ibuf | IBuf | 12.80 | 16.7% | 137.1 | 10.4% |
| alu | ALU | 7.21 | 9.4% | 85.3 | 6.5% |
| bpu | BreakpointUnit | 1.65 | 2.1% | 24.5 | 1.9% |

Reading the results
-------------------

- **Area** (core 1.34×, modules 0.87–2.32×): fastppa over-estimates a
  timing-closed commercial flow but stays within ~2× on most modules.
  The two worst modules (`ibuf` 2.32×, `csr` 1.90×) are register-array
  heavy; the uncosted-shaped array-write path documented as a known
  limitation in `DOCKER_VALIDATION.md` is the prime suspect. Note the
  comparison is not perfectly like-for-like: PrimeTime measures each
  module instance *inside* the routed core (after cross-boundary
  optimization, with top-level glue logic excluded — the five modules
  sum to 20297 of the core's 42015 µm²), while fastppa estimates each
  module standalone at its ports.
- **Delay** (1.95×): fastppa tracks single-pass logic synthesis, not a
  timing-closed physical design. On this same RTL, the open-source
  single-pass flow (Yosys+ABC+OpenSTA) gets 5.300 ns — fastppa is 1.10×
  of *that*; the remaining gap to PrimeTime's 2.989 ns is retiming, gate
  sizing, and buffering that no single-pass estimate replicates. See
  the Rocket section of `DOCKER_VALIDATION.md`.
- **Power**: absolute power is not comparable — PrimeTime used
  SAIF-derived switching activity at the flow's SDC clock, while
  fastppa defaults to 1 GHz with a 0.1 toggle rate (fastppa's whole-core
  total is 2287 mW vs PrimeTime's 151.4 mW under those mismatched
  assumptions). What can be compared is the *relative* per-module
  breakdown, which tracks: the ranking matches for the top modules and
  the shares are within a factor of ~1.6 (csr is over-weighted at 48.9%
  vs 31.8%, consistent with its area over-estimate).

What this file does not claim
-----------------------------

- No PrimeTime per-module *delay* numbers: the published reports do not
  contain per-module timing groups, so no such comparison is made.
- No speed benchmark against PrimeTime: the published reports do not
  include synthesis runtimes. fastppa-vs-Yosys runtimes are measured in
  `DOCKER_VALIDATION.md`.
- Accuracy against the open-source synthesis flow across 26 designs is
  measured separately (and reproducibly) in `DOCKER_VALIDATION.md`;
  this file is only about the one design with commercial ground truth.
