# New IC3 SAT Backend Benchmark on HWMCC 2017

This report compares the `ictminisat`, `minisat2`, and `cadical` SAT
backends for `ebmc --new-ic3` on the full HWMCC 2017 single-track suite.

## Setup

- Suite: `HWMCC 2017 single track`
- Compiler: `clang++`
- Build cache: `ccache`
- Timeout: `60` seconds per benchmark/backend
- Parallel jobs: `24`
- Host: `AMD EPYC 9R14, 48 cores, 92 GiB RAM`
- Build command: `env CCACHE_DIR=/tmp/ccache make -C src -j4 CXX='ccache clang++' MINISAT2=/local/home/dkr/3hw-cbmc/lib/cbmc/minisat-2.2.1 CADICAL=/local/home/dkr/3hw-cbmc/lib/cbmc/cadical`
- Benchmark command: `BENCH_DIR=/local/home/dkr/3hw-cbmc/benchmarking/hwmcc17-single JOBS=24 benchmarking/compare_new_ic3_sat_solvers.sh 60`
- Expected labels: `benchmarking/hwmcc17_single_expected.csv`
- Raw results: `benchmarking/hwmcc17_single_new_ic3_sat_backends.csv`

## Key Findings

- `minisat2` had the best known-label coverage at `107/166` correct solves, `+2` versus `ictminisat` and `+11` versus `cadical`.
- `minisat2` also had the best PAR-2 score at `44.86` seconds; on the `104` cases solved correctly by both MiniSAT-based backends, `ictminisat` vs `minisat2` yielded a `1.05x` geomean speedup for `ictminisat`, so `minisat2` wins overall by solving two additional known-label cases rather than by being faster on the shared subset.
- `cadical` solved fewer known-label cases (`96/166`, `-9` versus `ictminisat`) but did contribute `1` unique correct solve(s): `139444p22`.
- Wrong decisive results observed: `0`.

## Recommendation

- Keep SAT-backend selection user-visible via `--new-ic3-sat-solver`.
- If we want to change the default based on HWMCC 2017 alone, `minisat2` is the strongest candidate on solved-count grounds and `minisat2` is best on PAR-2.
- Keep `cadical` as an opt-in backend rather than the default; it offers niche coverage gains but loses materially on aggregate throughput.

## Corpus Summary

| total | expected proved | expected refuted | expected unknown |
| --- | --- | --- | --- |
| 300 | 111 | 55 | 134 |

## Overall Outcome Counts

| backend | proved | refuted | timeout | error | missing |
| --- | --- | --- | --- | --- | --- |
| ictminisat | 78 | 28 | 192 | 2 | 0 |
| minisat2 | 80 | 28 | 191 | 1 | 0 |
| cadical | 70 | 27 | 201 | 2 | 0 |

## Known-Label Accuracy

| backend | correct decisive | wrong decisive | unsolved known | known solved rate |
| --- | --- | --- | --- | --- |
| ictminisat | 105 | 0 | 61 | 63.3% |
| minisat2 | 107 | 0 | 59 | 64.5% |
| cadical | 96 | 0 | 70 | 57.8% |

## Unknown-Label Behavior

| backend | decisive on unknown | timeout unknown | error unknown |
| --- | --- | --- | --- |
| ictminisat | 1 | 133 | 0 |
| minisat2 | 1 | 133 | 0 |
| cadical | 1 | 133 | 0 |

## Runtime Summary

Correct decisive runtimes use the CSV's centisecond timing. PAR scores are
computed on the 166 known-label benchmarks with penalties
of `120` seconds for PAR-2 and
`600` seconds for PAR-10.

| backend | median s | geomean s | mean s | PAR-2 | PAR-10 |
| --- | --- | --- | --- | --- | --- |
| ictminisat | 0.27 | 0.31 | 2.47 | 45.66 | 222.05 |
| minisat2 | 0.27 | 0.35 | 3.44 | 44.86 | 215.47 |
| cadical | 0.38 | 0.36 | 3.61 | 52.69 | 255.10 |

## Unique Correct Solves

| backend | unique correct solves |
| --- | --- |
| ictminisat | 1 |
| minisat2 | 3 |
| cadical | 1 |

## Pairwise Shared Correct Solves

Geomean speedup is reported for the left backend over the right backend;
values above `1.00` favor the left backend.

| pair | shared correct | left wins | right wins | ties | geomean speedup |
| --- | --- | --- | --- | --- | --- |
| ictminisat vs minisat2 | 104 | 42 | 35 | 27 | 1.05 |
| ictminisat vs cadical | 95 | 73 | 11 | 11 | 1.59 |
| minisat2 vs cadical | 95 | 71 | 13 | 11 | 1.52 |

## Notable Benchmarks

| benchmark | expected | fastest backend | fastest time (s) | results | note |
| --- | --- | --- | --- | --- | --- |
| beemadd4b1 | refuted | ictminisat | 56.52 | ictminisat: refuted@56.52s; minisat2: timeout@-s; cadical: timeout@-s | unique correct solve by ictminisat |
| 6s380b511 | refuted | minisat2 | 14.63 | ictminisat: timeout@-s; minisat2: refuted@14.63s; cadical: timeout@-s | unique correct solve by minisat2 |
| bobsmi2c | proved | minisat2 | 29.35 | ictminisat: timeout@-s; minisat2: proved@29.35s; cadical: timeout@-s | unique correct solve by minisat2 |
| 6s221rb14 | proved | minisat2 | 48.47 | ictminisat: timeout@-s; minisat2: proved@48.47s; cadical: timeout@-s | unique correct solve by minisat2 |
| 139444p22 | refuted | cadical | 13.14 | ictminisat: timeout@-s; minisat2: timeout@-s; cadical: refuted@13.14s | unique correct solve by cadical |
| 6s344rb054 | proved | minisat2 | 2.09 | ictminisat: proved@2.44s; minisat2: proved@2.09s; cadical: proved@24.63s | minisat2 faster than cadical by 11.78x; ictminisat faster than cadical by 10.09x |
| 6s276rb342 | proved | minisat2 | 5.03 | ictminisat: proved@5.67s; minisat2: proved@5.03s; cadical: proved@47.86s | minisat2 faster than cadical by 9.51x; ictminisat faster than cadical by 8.44x |
| pj2016 | proved | minisat2 | 4.43 | ictminisat: proved@4.74s; minisat2: proved@4.43s; cadical: proved@41.34s | minisat2 faster than cadical by 9.33x; ictminisat faster than cadical by 8.72x |
| 6s372rb26 | proved | ictminisat | 10.15 | ictminisat: proved@10.15s; minisat2: proved@16.41s; cadical: proved@58.51s | ictminisat faster than cadical by 5.76x |
| bob3 | proved | ictminisat | 10.61 | ictminisat: proved@10.61s; minisat2: proved@58.51s; cadical: proved@37.60s | ictminisat faster than minisat2 by 5.51x |
| pdtvisblackjack0 | proved | minisat2 | 0.15 | ictminisat: proved@0.19s; minisat2: proved@0.15s; cadical: proved@0.80s | minisat2 faster than cadical by 5.33x; ictminisat faster than cadical by 4.21x |

## Sanity Checks

| backend | blank decisive seconds | nonblank nonsolved seconds |
| --- | --- | --- |
| ictminisat | 0 | 0 |
| minisat2 | 0 | 0 |
| cadical | 0 | 0 |
