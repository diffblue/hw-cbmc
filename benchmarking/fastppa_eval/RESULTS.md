# Results for the model of PR #1927

The model is the estimator of PR #1927, with main merged and the fixes of
this branch, at commit ecaffcb3. It is run as `fastppa <files> --top <top>
--process 45nm`, and its "Reg-to-reg delay" is compared.

Ground truth G1 was produced with `openroad/orfs@sha256:13f2e9da79b0`
(Yosys 0.68, OpenROAD with OpenSTA), with the NanGate45 typical liberty.
The raw data and full reports, including every excluded design and the
reason for its exclusion, are in `results/`.

The error of an estimate is max(r, 1/r), where r = estimate / truth.

## E1: LogikBench (held out)

Of the 157 designs, fastppa handles 142, and 139 of them have a G1 result.

| Comparison | geomean ratio | median error | p90 error | within 1.5x | within 2x | Spearman |
|---|---|---|---|---|---|---|
| Area vs G1 | 3.31 | 2.68x | 28.0x | 27% | 40% | 0.81 |
| Delay vs G1 | 1.32 | 1.79x | 9.03x | 37% | 55% | 0.73 |
| Area vs G2 | 3.03 | 2.36x | 32.1x | 34% | 46% | 0.80 |
| Delay vs G2 (1/fmax) | 1.98 | 2.08x | 16.0x | 27% | 48% | 0.66 |

The largest area errors are overestimates:

| Design | Error |
|---|---|
| `arithmetic/sine` | 34,766x (15.3 mm² estimated, 439 µm² synthesized) |
| `arithmetic/addtree` | 448x |
| `basic/muxhot` | 423x |
| `basic/muxpri` | 385x |
| `basic/muxcase` | 161x |
| `blocks/sad8x8` | 160x |
| `blocks/lfsr` | 149x |

Of the 15 designs fastppa does not handle, 4 are frontend syntax errors,
6 end in an internal error (exit 6), 2 in a conversion error, and 3 time
out after 120 s.

## E2: regression/fastppa (in sample)

The model was tuned on these designs. Two of the 28 designs, `const_index`
and `counter`, synthesize to no cells, so their ratios are not defined.

| Comparison | geomean ratio | median error | p90 error | within 1.5x | within 2x | Spearman |
|---|---|---|---|---|---|---|
| Area vs G1 | 1.14 | 1.32x | 2.03x | 58% | 88% | 0.92 |
| Delay vs G1 | 1.02 | 1.22x | 1.91x | 73% | 92% | 0.87 |

## C: single-operator designs

These are 139 designs, each with one operator at one width.

| Comparison | geomean ratio | median error | p90 error | within 2x |
|---|---|---|---|---|
| Area vs G1 | 2.47 | 1.41x | 48.6x | 68% |
| Delay vs G1 | 1.49 | 1.60x | 7.17x | 66% |

The large errors in C are reads from arrays with a variable index. For
example, a 64-entry array of 32-bit words is estimated at 3,813,830 µm²,
and synthesizes to 1,906 µm².
