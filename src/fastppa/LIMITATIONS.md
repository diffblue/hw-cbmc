Known limitations
=================

Numbers are from `benchmarking/fastppa_eval/RESULTS.md` (45nm unless
stated). The error factor of an estimate is max(r, 1/r) with r =
estimate / synthesis.

Accuracy
--------

- **Area is too large on the held-out set E3.** On the 58 E3 designs,
  graph areas are 2.28x synthesis on average (median error 2.25x), with a
  rank correlation of 0.97. The error is systematic rather than random;
  its cause is being investigated. On E1 the bias is 1.74x.
- **Logic that synthesis minimises at the bit level** is overestimated by
  the word-level model: tables of constants (`memory/rom`, 21x), XOR
  networks selected by elaboration-time masks (`blocks/lfsr`, 67x). The
  `--netlist` estimate avoids some of this.
- **`--netlist` delays are too short** (median ratio 0.25 on E3): the AIG
  is not restructured, and a 2-input AND gate is a poor stand-in for the
  cells ABC maps to. Use `--netlist` for area only.
- **Data power** is fitted per operator with random inputs at a fixed
  toggle rate; it does not see glitches or correlated activity. Median
  error 1.77x on E3.
- **No wires, placement or clock tree.** Delays are cell delays only.
  For the Rocket core, PrimeTime's post-route critical path is 2.99 ns
  and fastppa's estimate 3.77 ns.
- **Comparators on the same operands are not shared**: `a < b`, `a == b`
  and `a > b` are costed as three comparators
  (`regression/fastppa/bugs/shared_comparator_bug`, KNOWNBUG).
- **No memory macros.** Arrays are flip-flops and muxes.

Process nodes
-------------

- **Derived tables are poor where they can be checked.** Deriving the
  130nm and 7nm tables from NanGate45 with DeepScaleTool's factors and
  comparing with the measured sky130, IHP SG13G2 and ASAP7 tables on E1:
  - area: 7nm is 0.22x of ASAP7 synthesis (median error 5.75x); 130nm is
    2.83x of sky130 and 1.57x of IHP;
  - leakage: off by factors of 5 (7nm) to over 10^5 (sky130), because
    leakage per µm² differs by orders of magnitude between libraries;
  - clock energy: off by 1.8x to 3.7x;
  - delay and data energy are within the error of the measured tables.
  The `90nm`, `65nm`, `28nm`, `14nm`, `5nm` and `3nm` tables should
  therefore be read as rough relative figures, and their leakage not at
  all.
- **ASAP7 and GT2N are predictive PDKs**, not production processes.
- **One corner, one threshold voltage, one track height** per library
  (typical; see `benchmarking/fastppa_eval/platforms.sh`).

Unsupported designs
-------------------

Of the 250 LogikBench designs (E1 and E3), the word-level estimator fails
on 53:

- 26 in EBMC's front end: 18 "CONVERSION ERROR", 8 syntax errors;
- 12 in fastppa: 8 combinational loops through wires whose parts depend
  on other parts in ways the graph does not resolve, 4 state constraints
  it does not understand (conditional or indexed left-hand sides, a
  primitive module);
- 10 end with an internal error (exit code 6) or a failed assertion, not
  yet attributed to the front end or to fastppa;
- 5 time out after 120 s.

The reports in `benchmarking/fastppa_eval/results/` list every design and
the reason.
