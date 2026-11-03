# Performance

Comparison of the new IC3 engine (`--new-ic3`) against the in-tree
bit-level IC3 engine (`--ic3`, src/ic3), [rIC3](https://github.com/gipsyh/rIC3)
and [Pono](https://github.com/stanford-centaur/pono).

## Setup

* Machine: Apple M2 Max, 64 GB RAM, macOS 26.5
* Timeout: 60 seconds per benchmark and tool; wall-clock time in seconds,
  including front-end
* Benchmarks: 49-benchmark sample of HWMCC08 (every 12th benchmark of the
  585 SMV translations in `benchmarking/hwmcc08public-smv/`,
  in alphabetical order)
* Tools and configurations:
  * ebmc `--ic3` (built from this PR's sources) on the SMV translations.
    Note: this engine only accepts `sva_always` properties; for these runs
    `ic3_supports_property` in `src/ic3/m1ain.cc` was locally extended to
    accept `AG`/`G` (see the note in `benchmarking/compare_ic3.sh`).
  * ebmc `--new-ic3` (built from this PR's sources) on the SMV translations.
  * rIC3 1.5.2 (`ric3 check <file>.aig ic3`, single-threaded IC3 engine)
    on the original AIGER files.
  * Pono e60007f (`pono -e ic3bits -k 10000`, bit-level IC3 with Bitwuzla)
    on the SMV translations, with `SPEC AG p` rewritten to `INVARSPEC p;`
    (Pono's SMV front-end does not accept CTL specs).

All verdicts agree across all four tools, and match the expected results
published for HWMCC08 (`benchmarking/hwmcc08results.csv`; see
`benchmarking/validate_new_ic3.sh`).

## Summary

| tool | solved (of 49) | timeouts | total time on solved | fastest solver |
|---|---:|---:|---:|---:|
| ebmc `--ic3` | 45 | 4 | 220.0 s | 5 |
| ebmc `--new-ic3` | 43 | 6 | 99.2 s | 20 |
| rIC3 | 48 | 1 | 41.1 s | 35 |
| Pono (ic3bits) | 34 | 15 | 243.8 s | 1 |

Head-to-head of the two ebmc engines: 42 benchmarks are solved by both;
the new engine is faster on 27 of them. The new engine uniquely solves
139462p24; the old engine uniquely solves 139453p22, bc57sensorsp2 and
prodcellp2 — all three are refutations with deep counterexamples, which
is the main remaining weakness of the new engine (its per-frame blocking
effort makes frontier advancement expensive when a counterexample is more
than ~50 frames deep).

rIC3 remains substantially ahead of both ebmc engines; it is the source
of several of the techniques used in the new engine.

## Update: decision-variable restriction and eager clause pushing

Two further optimizations:

1. *Decision-variable restriction*: the per-frame MiniSAT solvers only
   branch on latch and input variables. The AIG gates use the full
   3-clause Tseitin encoding, so BCP totalizes any assignment of the
   latches and inputs; models remain genuine.
2. *Eager clause pushing*: after MIC generalization, the blocking phase
   pushes the generalized clause to the highest frame where it is still
   relatively inductive — one SAT query per level — instead of
   re-running a full MIC generalization each time the obligation is
   re-queued one level higher.

A third experiment, VSIDS-style decay of the MIC literal-activity
ordering, improved eijkbs3330 but caused a reproducible 15x regression
on 139453p22 and was dropped.

### Setup

* Machine: Apple M2 Max, 64 GB RAM, macOS 26.5.1
* Timeout: 60 seconds wall-clock per benchmark, including front-end
* All runs read the original AIGER files with ebmc's native AIGER
  front-end (not the SMV translations used above)
* Configurations, all `--new-ic3`:
  * *base*: main at 5d8e0a1a
  * *push*: base + eager clause pushing
  * *both*: base + eager clause pushing + decision-variable restriction
    (this PR)
* Benchmark sets:
  * HWMCC'08: the 49-benchmark sample above, run sequentially; expected
    verdicts from `hwmcc08results.csv`
  * HWMCC'17: all 300 single-property benchmarks, 4 parallel workers;
    expected verdicts are the consensus of the 14 HWMCC'17 solvers,
    available for 242 of the 300 (no solver disagreed on any of them)
  * HWMCC'25 bit-level safety track: 142-benchmark sample — every 2nd
    (in alphabetical order, starting with the first) of the 284
    benchmarks with a definitive competition verdict — 2 parallel
    workers
* 13 HWMCC'17 benchmarks (intel012/013/027/028/036/039/040/043 and
  oski15a01b00s/a01b57s/a07b0s/a08b00s/a08b08s) overflow the default
  8 MB stack in the recursion of `convert_trans_to_netlistt`, before
  the engine starts, with every configuration and with `--ic3`. These
  were run with `ulimit -s 65520`.

No configuration reported a wrong verdict on any of the three sets.

### Results

| configuration | HWMCC'08 (of 49) | HWMCC'17 (of 300) | HWMCC'25 (of 142) |
|---|---:|---:|---:|
| base | 43 | 115 | 70 |
| push | 43 | 119 | 72 |
| both (this PR) | 46 | 120 | 70 |

Total time on the benchmarks solved by all three configurations:

| configuration | HWMCC'08 (42) | HWMCC'17 (109) | HWMCC'25 (63) |
|---|---:|---:|---:|
| base | 93.3 s | 333.8 s | 362.6 s |
| push | 94.1 s | 291.1 s | 258.7 s |
| both (this PR) | 33.2 s | 228.7 s | 318.2 s |

HWMCC'08: the PR newly solves 139454p23 (24.0 s), csmacdp2 (43.0 s)
and prodcellp2 (46.7 s); largest improvements over base are
139453p22 38.4 → 1.8 s, neclaftp1001 23.3 → 0.7 s and nusmvtcasp5
18.1 → 5.9 s. Eager pushing alone is neutral on this set; the gain
comes from combining it with the decision-variable restriction.

HWMCC'17: the PR solves 9 benchmarks that base does not (among them
139444p22, csmacdp2, intel026, intel056, intel061 and
productioncellp0), and is faster on 63 of the 111 commonly solved.

The decision-variable restriction is not uniformly beneficial.
It turns 4 HWMCC'17 solves into timeouts — 6s120 (0.8 s), 6s421rb083 (0.5 s), bobunr2p10d40l (0.1 s),
6s221rb14 (30.4 s) — where a single SAT query at frame 1 does not
terminate; without the restriction all four are solved as before. On
HWMCC'25 it costs a net 2 benchmarks relative to *push* (5 gained,
7 lost, the latter mostly hkust miters), and several instances slow
down by 10x or more (e.g. collision.1.prop1-func-interl 2.0 → 47.3 s).
Restricting decisions to inputs and latches can make the SAT search
exponentially harder on circuits where branching on internal gates
pays off.

Comparison with the in-tree `--ic3` engine on HWMCC'17 (same
machine, 4 workers, built from this PR):

| engine | solved (of 300) | proved / refuted | total time on solved | wrong verdicts |
|---|---:|---:|---:|---:|
| ebmc `--ic3` | 126 | 92 / 34 | 617 s | 0 |
| ebmc `--new-ic3` | 120 | 87 / 33 | 588 s | 0 |

Of the 116 benchmarks solved by both engines, the new engine is
faster on 84. The old engine solves 10 uniquely (among them
bc57sensorsp2, prodcellp4, irstdme6 and three of the
decision-restriction regressions above), the new engine 4. `--ic3`
reports 6s128 as not supported (no latches).

For scale, on the HWMCC'25 sample rIC3 solved 112 within 60 s in the
competition (on different hardware).

## Reproducing

    # ebmc engines + rIC3 + Pono, CSV output
    cd benchmarking
    ./compare4way.sh 60 <benchmark>...

    # just the two ebmc engines, table output
    ./compare_ic3.sh 60 <benchmark>...

    # check --new-ic3 verdicts against the published HWMCC08 results
    ./validate_new_ic3.sh 60 <benchmark>...

## Full results

Times in seconds; t/o = timeout (60 s).

| benchmark | verdict | ebmc `--ic3` | ebmc `--new-ic3` | rIC3 | Pono |
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
