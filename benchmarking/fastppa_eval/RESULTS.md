# Results

Protocol: `PROTOCOL.md`. Raw data: `results/` (ground truth in `gt/`,
estimates in `est/`, full reports with every excluded design in
`reports/`).

- Models: `pr1927` is the estimator of PR #1927 (at d81cdd01); `graph` is
  the word-level estimator and `netlist` is `fastppa --netlist`, both at
  44d1ca8a, the commit at which they were frozen before the first run on
  E3.
- Ground truth G1: Yosys 0.68 + ABC and OpenSTA from
  `openroad/orfs@sha256:13f2e9da79b0`, with the libraries of
  `platforms.sh`. Energies are per cycle of a 50 ns clock: clock energy
  with constant inputs, data energy per unit of input toggle rate.
- The error of an estimate is max(r, 1/r), r = estimate / truth.
  "bias" is the geometric mean of r; "w2" is the share of designs with an
  error of at most 2x.

## E3 (held out; NanGate45)

93 LogikBench designs; 58 are handled by all three models and the
ground-truth flow.

| Quantity | Model | bias | median error | p90 error | w2 | Spearman |
|---|---|---|---|---|---|---|
| Area | pr1927 | 3.54 | 3.21x | 6.21x | 19% | 0.95 |
| | graph | 2.28 | 2.25x | 2.87x | 38% | 0.97 |
| | netlist | 0.51 | 1.60x | 6.44x | 60% | 0.94 |
| Delay | pr1927 | 0.98 | 1.61x | 2.66x | 74% | 0.84 |
| | graph | 0.94 | 1.27x | 2.39x | 84% | 0.87 |
| | netlist | 0.23 | 4.01x | 9.01x | 3% | 0.84 |
| Clock energy (31 designs with registers) | pr1927 | 40.4 | 35.7x | | 0% | 0.89 |
| | graph | 0.80 | 1.53x | | 97% | 0.99 |
| Data energy | pr1927 | 238 | 204x | | 0% | 0.88 |
| | graph | 1.25 | 1.77x | | 62% | 0.92 |
| Leakage | pr1927 | 16.3 | 15.5x | | 0% | 0.95 |
| | graph | 2.40 | 2.35x | | 33% | 0.97 |

Against LogikBench's published results (G2) on 54 of these designs, graph
has a median area error of 1.96x and a median delay error (1/fmax) of
1.26x; pr1927 2.90x and 1.67x.

By group, the graph area bias is 2.70 (epfl, 16 designs), 2.10 (iscas85,
11), 1.89 (iscas89, 28) and 7.35 (koios, 3).

## E1 (NanGate45; in sample for the rules of 6e0f3857)

157 designs, 130 compared. The rules for aligned selects, shifts by
multiples and conditional writes were found by looking at E1 results.

| Quantity | Model | bias | median error | w2 | Spearman |
|---|---|---|---|---|---|
| Area | pr1927 | 2.96 | 2.50x | 43% | 0.82 |
| | graph | 1.74 | 1.41x | 72% | 0.95 |
| | netlist | 1.06 | 1.34x | 84% | 0.92 |
| Delay | pr1927 | 1.32 | 1.78x | 55% | 0.75 |
| | graph | 0.89 | 1.66x | 66% | 0.77 |
| | netlist | 0.28 | 2.54x | 36% | 0.59 |
| Clock energy (57 designs) | graph | 0.75 | 1.42x | 98% | 0.99 |
| Data energy | graph | 1.55 | 1.76x | 61% | 0.90 |
| Leakage | graph | 1.75 | 1.41x | 72% | 0.95 |

## E1 with the other cell libraries (graph)

Each library's table was fitted on that library's calibration designs
only.

| Library | Area median / w2 | Delay median / w2 | Clock energy median | Data energy median | Leakage median |
|---|---|---|---|---|---|
| gf180 | 1.35x / 72% | 1.57x / 66% | 1.01x | 1.84x | 1.39x |
| sky130 | 1.44x / 68% | 1.78x / 56% | 1.11x | 1.86x | 1.55x |
| ihp-sg13g2 | 1.40x / 72% | 1.68x / 65% | 1.11x | 1.86x | 1.50x |
| nangate45 | 1.41x / 72% | 1.66x / 66% | 1.42x | 1.76x | 1.41x |
| asap7 | 1.43x / 68% | 1.80x / 58% | 1.07x | 1.67x | 1.47x |
| gt2n | 1.44x / 69% | 1.72x / 60% | 1.00x | 1.65x | 1.80x |

## Derived tables

Where a measured table exists at the target, the derivation of
`derive.py` can be checked: the NanGate45 table scaled to 130nm and 7nm,
against synthesis with sky130, IHP SG13G2 and ASAP7, on E1 (graph):

| Target | Area bias (measured table) | Delay bias | Clock energy bias | Leakage bias |
|---|---|---|---|---|
| sky130 | 2.83 (1.80) | 0.57 (1.06) | 0.36 (1.01) | 1.8·10^5 (1.99) |
| ihp-sg13g2 | 1.57 (1.75) | 0.87 (1.14) | 0.29 (1.17) | 2.8·10^3 (1.84) |
| asap7 | 0.22 (1.80) | 0.95 (1.02) | 0.60 (1.03) | 6.10 (1.82) |

Delay and data energy scale acceptably; area, clock energy and above all
leakage do not.

## E2 (regression/fastppa; in sample for pr1927)

26 of 28 designs (two synthesize to no cells).

| Quantity | Model | median error | w2 |
|---|---|---|---|
| Area | pr1927 | 1.32x | 88% |
| | graph | 1.34x | 85% |
| | netlist | 1.31x | 96% |
| Delay | pr1927 | 1.22x | 92% |
| | graph | 1.16x | 81% |
| Data energy | pr1927 | 76.3x | 0% |
| | graph | 1.41x | 77% |

## Rocket core (PrimeTime, post-route, NanGate45)

From `benchmarking/rocket_core/compare_primetime.py`:

| Quantity | PrimeTime | graph | ratio |
|---|---|---|---|
| Cell area | 42,015 µm² | 49,951 µm² | 1.19 |
| Critical path | 2.989 ns | 3.774 ns | 1.26 |

PrimeTime reports 151.4 mW with SAIF activity at an unknown clock
frequency, so power is not compared.
