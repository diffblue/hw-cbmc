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
- Build command: `env CCACHE_DIR=/tmp/ccache make -C src -j16 CXX='ccache clang++' MINISAT2=/local/home/dkr/hw-cbmc/lib/cbmc/minisat-2.2.1 CADICAL=/local/home/dkr/3hw-cbmc/lib/cbmc/cadical`
- Benchmark command: `BENCH_DIR=/local/home/dkr/3hw-cbmc/benchmarking/hwmcc17-single JOBS=24 benchmarking/compare_new_ic3_sat_solvers.sh 60`
- Expected labels: `benchmarking/hwmcc17_single_expected.csv`
- Raw results: `benchmarking/hwmcc17_single_new_ic3_sat_backends.csv`

## Key Findings

- `minisat2` had the best known-label coverage at `109/166` correct solves, `+4` versus `ictminisat` and `+13` versus `cadical`.
- `minisat2` also had the best PAR-2 score at `43.52` seconds; on the `105` cases solved correctly by both MiniSAT-based backends, `ictminisat` vs `minisat2` yielded a `1.03x` geomean speedup for `ictminisat`, so `minisat2` wins overall by solving 4 additional known-label case(s) rather than by being faster on the shared subset.
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
| minisat2 | 81 | 29 | 187 | 3 | 0 |
| cadical | 70 | 27 | 200 | 3 | 0 |

## Known-Label Accuracy

| backend | correct decisive | wrong decisive | unsolved known | known solved rate |
| --- | --- | --- | --- | --- |
| ictminisat | 105 | 0 | 61 | 63.3% |
| minisat2 | 109 | 0 | 57 | 65.7% |
| cadical | 96 | 0 | 70 | 57.8% |

## Unknown-Label Behavior

| backend | decisive on unknown | timeout unknown | error unknown |
| --- | --- | --- | --- |
| ictminisat | 1 | 132 | 1 |
| minisat2 | 1 | 132 | 1 |
| cadical | 1 | 132 | 1 |

## Runtime Summary

Correct decisive runtimes use the CSV's centisecond timing. PAR scores are
computed on the 166 known-label benchmarks with penalties
of `120` seconds for PAR-2 and
`600` seconds for PAR-10.

| backend | median s | geomean s | mean s | PAR-2 | PAR-10 |
| --- | --- | --- | --- | --- | --- |
| ictminisat | 0.23 | 0.25 | 1.88 | 45.28 | 221.67 |
| minisat2 | 0.22 | 0.30 | 3.52 | 43.52 | 208.34 |
| cadical | 0.26 | 0.29 | 2.88 | 52.27 | 254.68 |

## Unique Correct Solves

| backend | unique correct solves |
| --- | --- |
| ictminisat | 0 |
| minisat2 | 4 |
| cadical | 1 |

## Pairwise Shared Correct Solves

Geomean speedup is reported for the left backend over the right backend;
values above `1.00` favor the left backend.

| pair | shared correct | left wins | right wins | ties | geomean speedup |
| --- | --- | --- | --- | --- | --- |
| ictminisat vs minisat2 | 105 | 30 | 37 | 38 | 1.03 |
| ictminisat vs cadical | 95 | 73 | 8 | 14 | 1.60 |
| minisat2 vs cadical | 95 | 75 | 7 | 13 | 1.56 |

## Notable Benchmarks

| benchmark | expected | fastest backend | fastest time (s) | results | note |
| --- | --- | --- | --- | --- | --- |
| 6s380b511 | refuted | minisat2 | 8.86 | ictminisat: timeout@-s; minisat2: refuted@8.86s; cadical: timeout@-s | unique correct solve by minisat2 |
| bobsmi2c | proved | minisat2 | 23.46 | ictminisat: timeout@-s; minisat2: proved@23.46s; cadical: timeout@-s | unique correct solve by minisat2 |
| 6s221rb14 | proved | minisat2 | 37.92 | ictminisat: timeout@-s; minisat2: proved@37.92s; cadical: timeout@-s | unique correct solve by minisat2 |
| bob05 | proved | minisat2 | 54.02 | ictminisat: timeout@-s; minisat2: proved@54.02s; cadical: timeout@-s | unique correct solve by minisat2 |
| 139444p22 | refuted | cadical | 10.61 | ictminisat: timeout@-s; minisat2: timeout@-s; cadical: refuted@10.61s | unique correct solve by cadical |
| 6s276rb342 | proved | minisat2 | 3.81 | ictminisat: proved@4.28s; minisat2: proved@3.81s; cadical: proved@38.41s | minisat2 faster than cadical by 10.08x; ictminisat faster than cadical by 8.97x |
| pj2016 | proved | minisat2 | 5.15 | ictminisat: proved@5.41s; minisat2: proved@5.15s; cadical: proved@43.08s | minisat2 faster than cadical by 8.37x; ictminisat faster than cadical by 7.96x |
| 6s344rb054 | proved | minisat2 | 1.65 | ictminisat: proved@1.67s; minisat2: proved@1.65s; cadical: proved@11.27s | minisat2 faster than cadical by 6.83x; ictminisat faster than cadical by 6.75x |
| 6s372rb26 | proved | ictminisat | 7.21 | ictminisat: proved@7.21s; minisat2: proved@11.53s; cadical: proved@41.05s | ictminisat faster than cadical by 5.69x |
| pdtvisblackjack0 | proved | minisat2 | 0.15 | ictminisat: proved@0.19s; minisat2: proved@0.15s; cadical: proved@0.82s | minisat2 faster than cadical by 5.47x |
| 6s421rb083 | proved | minisat2 | 0.85 | ictminisat: proved@0.91s; minisat2: proved@0.85s; cadical: proved@4.50s | minisat2 faster than cadical by 5.29x |
| bob3 | proved | ictminisat | 8.72 | ictminisat: proved@8.72s; minisat2: proved@43.92s; cadical: proved@30.26s | ictminisat faster than minisat2 by 5.04x |

## Sanity Checks

| backend | blank decisive seconds | nonblank nonsolved seconds |
| --- | --- | --- |
| ictminisat | 0 | 0 |
| minisat2 | 0 | 0 |
| cadical | 0 | 0 |
