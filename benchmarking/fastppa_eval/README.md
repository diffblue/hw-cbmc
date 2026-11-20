# Evaluating fastppa against synthesis

These scripts compare fastppa's area and delay estimates with Yosys, ABC
and OpenSTA, following `PROTOCOL.md`. The results are in `RESULTS.md`, and
the raw data in `results/`.

Requirements: Docker with the `openroad/orfs` image, Python 3, and
`git`. The ground-truth flow runs in the container; fastppa runs on the
host.

## Steps

1. Get LogikBench and lambdalib, at the commits the protocol fixes:

       git clone https://github.com/zeroasiccorp/logikbench.git
       git -C logikbench checkout 58539b81d9c622a6b55a4cabde5d6b1288b9fe1e
       git clone --depth 1 --branch v0.13.1 \
         https://github.com/siliconcompiler/lambdalib.git

2. Write the manifest of the held-out designs (E1, E3) and of
   regression/fastppa (E2), and generate the calibration designs (C):

       ./make_manifest.py --logikbench logikbench --lambdalib lambdalib \
         --repo ../.. manifest.tsv
       ./gen_microbench.py C

3. Compute the ground truth for a cell library (`platforms.sh` lists
   them; about 20 minutes with 16 jobs for E1 and E2):

       PLATFORM=nangate45 ./run_gt.sh manifest.tsv gt-work gt_E.tsv 16
       for p in nangate45 sky130hd gf180 ihp-sg13g2 asap7 gt2n; do
         PLATFORM=$p ./run_gt.sh C/manifest.tsv gt-C-$p gt/gt_C_$p.tsv 16
       done

4. Regenerate the cost tables compiled into fastppa (fits the measured
   tables on C, derives the others), and rebuild fastppa:

       ./netlist_counts.py C/manifest.tsv ../../src/fastppa/fastppa \
         netlist_counts_C.tsv
       ./make_tables.sh C/params.tsv gt netlist_counts_C.tsv
       make -C ../../src/fastppa

5. Run fastppa and report:

       ./evaluate.py run manifest.tsv est_E.tsv --process 45nm \
         --model 'graph|../../src/fastppa/fastppa|Critical path|' \
         --model 'netlist|../../src/fastppa/fastppa|Critical path|--netlist'
       ./evaluate.py report est_E.tsv gt_E.tsv --set E3 \
         --g2 logikbench/results/syn/asic/yosys_freepdk45.json

   Give `--model` more than once to compare several binaries or options on
   the same designs. `--detail` lists the numbers for each design. For
   PR #1927's estimator, use the delay label `Reg-to-reg delay`.

## Files

- `PROTOCOL.md`: data sets, ground truth, metrics and rules.
- `PROCESS_NODES.md`: which process nodes, and where their tables come
  from.
- `make_manifest.py`: lists the designs of E1, E2 and E3.
- `gen_microbench.py`: writes the single-operator designs of C.
- `platforms.sh`: the cell libraries of the ground-truth flow.
- `gt_flow.sh`: synthesizes, times and measures the power of one design;
  runs in the container.
- `run_gt.sh`: runs `gt_flow.sh` over a manifest, in parallel, in one
  container.
- `netlist_counts.py`: AIG statistics of the calibration designs.
- `fit.py`: fits one cost table on the ground truth of C.
- `derive.py`: derives a table for a node without an open library.
- `make_tables.sh`: regenerates all compiled-in tables.
- `evaluate.py`: runs fastppa over a manifest, and computes the metrics.
