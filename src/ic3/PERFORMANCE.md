# Performance

Comparison of the IC3 engine (`--ic3`) against the old IC3 engine
(`--old-ic3`, src/old-ic3), [rIC3](https://github.com/gipsyh/rIC3)
and [Pono](https://github.com/stanford-centaur/pono).

## Setup

* Machine: Apple M2 Max, 64 GB RAM, macOS 26.5
* Timeout: 60 seconds per benchmark and tool; wall-clock time in seconds,
  including front-end
* Benchmarks: 49-benchmark sample of HWMCC08 (every 12th benchmark of the
  585 SMV translations in `benchmarking/hwmcc08public-smv/`,
  in alphabetical order)
* Tools and configurations:
  * ebmc `--old-ic3` (built from this PR's sources) on the SMV translations.
    Note: this engine only accepts `sva_always` properties; for these runs
    `old_ic3_supports_property` in `src/old-ic3/m1ain.cc` was locally extended to
    accept `AG`/`G` (see the note in `benchmarking/compare_ic3.sh`).
  * ebmc `--ic3` (built from this PR's sources) on the SMV translations.
  * rIC3 1.5.2 (`ric3 check <file>.aig ic3`, single-threaded IC3 engine)
    on the original AIGER files.
  * Pono e60007f (`pono -e ic3bits -k 10000`, bit-level IC3 with Bitwuzla)
    on the SMV translations, with `SPEC AG p` rewritten to `INVARSPEC p;`
    (Pono's SMV front-end does not accept CTL specs).

All verdicts agree across all four tools, and match the expected results
published for HWMCC08 (`benchmarking/hwmcc08results.csv`; see
`benchmarking/validate_ic3.sh`).

## Summary

| tool | solved (of 49) | timeouts | total time on solved | fastest solver |
|---|---:|---:|---:|---:|
| ebmc `--old-ic3` | 45 | 4 | 220.0 s | 5 |
| ebmc `--ic3` | 43 | 6 | 99.2 s | 20 |
| rIC3 | 48 | 1 | 41.1 s | 35 |
| Pono (ic3bits) | 34 | 15 | 243.8 s | 1 |

Head-to-head of the two ebmc engines: 42 benchmarks are solved by both;
the IC3 engine is faster on 27 of them. The IC3 engine uniquely solves
139462p24; the old engine uniquely solves 139453p22, bc57sensorsp2 and
prodcellp2 — all three are refutations with deep counterexamples, which
is the main remaining weakness of the IC3 engine (its per-frame blocking
effort makes frontier advancement expensive when a counterexample is more
than ~50 frames deep).

rIC3 remains substantially ahead of both ebmc engines; it is the source
of several of the techniques used in the IC3 engine.

## Reproducing

    # ebmc engines + rIC3 + Pono, CSV output
    cd benchmarking
    ./compare4way.sh 60 <benchmark>...

    # just the two ebmc engines, table output
    ./compare_ic3.sh 60 <benchmark>...

    # check --ic3 verdicts against the published HWMCC08 results
    ./validate_ic3.sh 60 <benchmark>...

## Full results

Times in seconds; t/o = timeout (60 s).

| benchmark | verdict | ebmc `--old-ic3` | ebmc `--ic3` | rIC3 | Pono |
|---|---|---:|---:|---:|---:|
| 139442p0 | proved | 0.10 | 0.07 | 0.07 | 2.22 |
| 139443p0neg | refuted | 0.94 | 1.65 | 0.21 | 8.59 |
| 139444p1 | refuted | 1.63 | 1.66 | 0.30 | 20.23 |
| 139452p1neg | refuted | 1.42 | 0.76 | 0.22 | 10.11 |
| 139453p22 | refuted | 36.62 | t/o | 0.46 | t/o |
| 139454p23 | refuted | t/o | t/o | 1.40 | t/o |
| 139462p24 | refuted | t/o | 12.83 | 1.01 | t/o |
| 139463p5 | refuted | 4.65 | 4.58 | 0.68 | 45.19 |
| 139464p5neg | refuted | 7.32 | 7.30 | 1.25 | t/o |
| bc57sensorsp2 | refuted | 58.67 | t/o | 17.08 | t/o |
| bj08amba2g82 | proved | 0.04 | 0.03 | 0.04 | 0.10 |
| bj08aut5 | proved | 0.02 | 0.02 | 0.02 | 0.03 |
| bj08vsar6 | refuted | 0.06 | 0.04 | 0.04 | 0.05 |
| brpp1neg | refuted | 0.06 | 0.05 | 0.06 | 0.56 |
| csmacdp2 | refuted | 58.24 | 1.26 | 0.23 | t/o |
| dme5p1 | refuted | 0.12 | 0.05 | 0.07 | 0.45 |
| eijkbs3330 | proved | 5.89 | 20.64 | 0.91 | t/o |
| eijkS349 | proved | 0.37 | 0.39 | 0.20 | t/o |
| eijkS838 | proved | t/o | t/o | 0.95 | t/o |
| kenflashp08 | proved | 0.06 | 0.03 | 0.04 | 0.04 |
| neclaftp1001 | proved | 3.44 | 13.17 | 5.15 | t/o |
| nusmvbrp | proved | 0.90 | 1.45 | 0.21 | t/o |
| nusmvreactorp1 | proved | 0.04 | 0.03 | 0.02 | 0.03 |
| nusmvtcasp5 | refuted | 9.25 | 22.66 | 1.94 | t/o |
| pciptimoneg | refuted | 0.07 | 0.05 | 0.06 | 0.29 |
| pdtpmsmiim | proved | 1.22 | 1.27 | 0.06 | 8.95 |
| pdtpmsusbphy | proved | 0.03 | 0.03 | 0.04 | 0.04 |
| pdtvisblackjack3 | proved | 0.21 | 0.59 | 0.07 | 27.35 |
| pdtviseisenberg1 | proved | 0.81 | 0.32 | 0.12 | 45.76 |
| pdtvisgray0 | proved | 0.01 | 0.01 | 0.02 | 0.02 |
| pdtvisheap10 | proved | 0.04 | 0.03 | 0.03 | 0.04 |
| pdtvismiim1 | proved | 0.03 | 0.02 | 0.02 | 0.09 |
| pdtvisminmaxr3 | proved | 0.02 | 0.02 | 0.04 | 0.03 |
| pdtvisns3p02 | proved | 5.91 | 6.50 | 0.37 | t/o |
| pdtvisns3p14 | proved | 0.09 | 0.05 | 0.11 | 0.09 |
| pdtvisrethersqo0 | proved | 0.03 | 0.02 | 0.03 | 0.03 |
| pdtvistictactoe03 | refuted | 0.03 | 0.02 | 0.05 | 0.04 |
| pdtvistimeout1 | proved | 0.04 | 0.03 | 0.04 | 0.04 |
| pdtvisvending03 | proved | 0.04 | 0.03 | 0.03 | 0.03 |
| pdtvisvsa16a04 | proved | 0.25 | 0.29 | 0.08 | 0.77 |
| pdtvisvsa16a16 | proved | 0.13 | 0.07 | 0.02 | 0.09 |
| pdtvisvsa16a29 | ? | t/o | t/o | t/o | t/o |
| pdtvisvsar10 | proved | 0.53 | 0.33 | 0.07 | 34.95 |
| pdtvisvsar22 | proved | 0.06 | 0.04 | 0.04 | 0.05 |
| prodcellp2 | refuted | 18.16 | t/o | 6.97 | t/o |
| prodconspold1 | refuted | 2.03 | 0.53 | 0.16 | 36.09 |
| texasifetch1p3 | proved | 0.03 | 0.02 | 0.02 | 0.03 |
| texasPImainp12 | proved | 0.20 | 0.13 | 0.05 | 0.70 |
| viseisenberg | refuted | 0.17 | 0.09 | 0.04 | 0.71 |
