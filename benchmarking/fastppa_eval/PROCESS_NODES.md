# Process nodes

fastppa's cost tables come from synthesizing the calibration designs
(`gen_microbench.py`) to real cell libraries. Where no open cell library
exists for a node that matters in practice, the table is derived from a
measured one with published scaling factors.

## Which nodes

The foundry market is split between leading-edge FinFET/GAA nodes and
mature planar nodes:

- At TSMC, 3nm was 24%, 5nm 36% and 7nm 14% of wafer revenue in 2025;
  7nm and below were 74% in Q4 2025 (TSMC quarterly reports, as summarised
  by Tom's Hardware, 2026).
- Mature-node foundries (UMC, GlobalFoundries, SMIC) still had 36% of
  foundry revenue in 2025, with 28nm the strongest of the mature nodes
  (Astute Group, 2025).
- 130nm and 180nm are the nodes of the open PDKs (SkyWater, IHP,
  GlobalFoundries) used for open-source tape-outs, and of much mixed-signal
  and automotive work.

## Tables

| `--process` | Source | Kind |
|---|---|---|
| `gf180`, `180nm` | GF180MCU 9-track, 5 V, typical | measured |
| `sky130`, `130nm` | SkyWater sky130_fd_sc_hd, typical | measured |
| `ihp-sg13g2` | IHP SG13G2 (130nm BiCMOS), typical | measured |
| `nangate45`, `45nm` | Nangate Open Cell Library (FreePDK45), typical | measured |
| `asap7`, `7nm` | ASAP7 (predictive 7nm FinFET), RVT, typical | measured (predictive PDK) |
| `gt2n`, `2nm` | GT2N (predictive 2nm nanosheet), LVT, w31, typical | measured (predictive PDK) |
| `90nm`, `65nm`, `28nm`, `14nm` | `nangate45` with DeepScaleTool factors | derived |
| `5nm`, `3nm` | `asap7` with TSMC's published N7→N5→N3 figures | derived |

"Measured" tables are fitted by `fit.py` on the ground truth of the
calibration designs for that library, with the flow of `gt_flow.sh` and
the platform settings of `platforms.sh` (from OpenROAD-flow-scripts).

### Derived tables

DeepScaleTool (S. Sarangi and B. Baas, "DeepScaleTool: A Tool for the
Accurate Estimation of Technology Scaling in the Deep-Submicron Era",
ISCAS 2021; spreadsheet at https://sourceforge.net/projects/deepscaletool/,
version of 03/02/2021, SHA-256 561a3f8f…8df8) gives these values, relative
to its own reference node, fitted to published Intel and TSMC data:

| Node | Area | Delay | Energy |
|---|---|---|---|
| 130nm | 8.3 | 1.96 | 2.52 |
| 90nm | 3.94 | 1.31 | 1.51 |
| 65nm | 2.04 | 1.0 | 1.0 |
| 45nm | 1.0 | 0.81 | 0.63 |
| 28nm | 0.35 | 0.67 | 0.37 |
| 14nm | 0.08 | 0.60 | 0.19 |
| 7nm | 0.011 | 0.53 | 0.11 |

A table for node x is the `nangate45` table with areas multiplied by
Area(x)/Area(45nm), delays by Delay(x)/Delay(45nm), and energies by
Energy(x)/Energy(45nm). Leakage is scaled like area, i.e. leakage per
µm² is kept; DeepScaleTool has no leakage factors.

For 5nm and 3nm, TSMC states for N5 relative to N7: 1.8x logic density,
15% higher speed at the same power, 30% lower power at the same speed;
and for N3 relative to N5: 1.6x logic density, 10–15% higher speed, 25–30%
lower power (TSMC technology symposium 2020, as reported by Tom's Hardware
and AnandTech). The tables use area factors 1/1.8 and 1/1.6, delay factors
1/1.15 and 1/1.125, and energy factors 0.70 and 0.725, applied to `asap7`.

The derivation is checked where measured tables exist on both ends: see
`RESULTS.md`, "Derived tables".
