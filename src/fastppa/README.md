fastppa
=======

Purpose
-------

`fastppa` estimates area, delay, and power for Verilog/SystemVerilog designs
at a configurable process node (3nm to 130nm). It operates at the word
level, walking expression DAGs from the transition system without requiring
gate-level synthesis.

How It Works
------------

The module takes the transition system produced by the Verilog front-end
and decomposes it into per-register next-state functions. Each expression
node (adder, multiplier, shift, MUX, comparator, bitwise op) is costed by
bit-width using per-technology lookup tables:

- **Area** (µm²) — sum of operator areas across the design
- **Delay** (ns) — critical-path through the deepest expression DAG,
  plus a wire-delay heuristic based on √area and fan-out
- **Power** (mW) — dynamic + clock tree + leakage, at `--clock-freq`
  (default 1 GHz) and `--toggle-rate` (default 0.1)

The cost tables and heuristics are calibrated against real synthesis
(Yosys + ABC + OpenSTA, NanGate45); see `DOCKER_VALIDATION.md` for the
methodology, per-design results, and known limitations of the model.

Usage
-----

Area and delay estimate at 28nm:

    $ fastppa design.sv --top main --process 28nm

Include power estimate at 500 MHz:

    $ fastppa design.sv --top main --process 7nm --clock-freq 500e6

Technology Parameterization
---------------------------

Built-in nodes: `3nm`, `7nm`, `14nm`, `28nm`, `45nm`, `65nm`, `90nm`,
`130nm`.

Each node provides per-operator cost tables indexed by bit-width.

Limitations
-----------

- No placement or routing; wire delay is a heuristic, not a wire-load
  model.
- Operator costs assume generic standard-cell implementations.
- Register arrays are costed as flip-flops up to 4096 bits and at SRAM
  density above that; no memory-compiler macros.
- Power assumes uniform switching activity (scaled by an RTL-derived
  activity ratio).
- I/O pads and power grid are not modeled.
- No liveness analysis: registers that real synthesis would eliminate as
  dead are still costed (see `DOCKER_VALIDATION.md`).

File Structure
--------------

    src/fastppa/
    ├── README.md
    ├── DOCKER_VALIDATION.md         — validation methodology and results
    ├── COMPARISON.md                — vs real Synopsys PrimeTime data
    ├── Makefile
    ├── main.cpp
    ├── fastppa_parse_options.{h,cpp} — CLI
    ├── fastppa_frontend.{h,cpp}      — Verilog → transition system
    ├── fastppa_estimator.{h,cpp}     — orchestration + output
    ├── estimate.{h,cpp}              — core DAG walker
    ├── technology_db.{h,cpp}         — process cost tables
    └── benchmark_openroad.sh, benchmark_scaling.sh
