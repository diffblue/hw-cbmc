fastppa
=======

Purpose
-------

`fastppa` estimates area, delay, and power for Verilog/SystemVerilog designs
at a configurable process node (7nm, 14nm, 28nm, 45nm, 65nm, 90nm). It
operates at the word level, walking expression DAGs from the transition
system without requiring gate-level synthesis.

How It Works
------------

The module takes the transition system produced by the Verilog front-end
and decomposes it into per-register next-state functions. Each expression
node (adder, multiplier, shift, MUX, comparator, bitwise op) is costed by
bit-width using per-technology lookup tables:

- **Area** (µm²) — sum of operator areas across the design
- **Delay** (ns) — critical-path through the deepest expression DAG
- **Power** (mW) — dynamic + leakage, requires `--clock-freq`

Usage
-----

Area and delay estimate at 28nm:

    $ fastppa design.sv --top main --process 28nm

Include power estimate at 500 MHz:

    $ fastppa design.sv --top main --process 7nm --clock-freq 500e6

Technology Parameterization
---------------------------

Built-in nodes: `7nm`, `14nm`, `28nm`, `45nm`, `65nm`, `90nm`.

Each node provides per-operator cost tables indexed by bit-width. Custom
libraries can be supplied via `--cell-lib <path>`.

Limitations
-----------

- No placement, routing, or wire-load modeling.
- Operator costs assume generic standard-cell implementations.
- Memory arrays costed by total bit count (no SRAM distinction).
- Power assumes uniform switching activity.
- Clock tree, I/O pads, and power grid are not modeled.

File Structure
--------------

    src/fastppa/
    ├── README.md
    ├── Makefile
    ├── main.cpp
    ├── fastppa_parse_options.h
    └── fastppa_parse_options.cpp
