# Evaluating fastppa against synthesis

These scripts compare fastppa's area and delay estimates with Yosys, ABC
and OpenSTA, following `PROTOCOL.md`. The results for the current model
are in `RESULTS.md`, and the raw data are in `results/`.

Requirements: Docker with the `openroad/orfs` image, Python 3, and
`git`. The ground-truth flow runs in the container; fastppa runs on the
host.

## Steps

1. Get LogikBench and lambdalib, at the commits the protocol fixes:

       git clone https://github.com/zeroasiccorp/logikbench.git
       git -C logikbench checkout 58539b81d9c622a6b55a4cabde5d6b1288b9fe1e
       git clone --depth 1 --branch v0.13.1 \
         https://github.com/siliconcompiler/lambdalib.git

2. Write the manifests of the held-out designs (E1, E2) and of the
   calibration designs (C):

       ./make_manifest.py --logikbench logikbench --lambdalib lambdalib \
         --repo ../.. manifest.tsv
       ./gen_microbench.py C

3. Compute the ground truth (about 20 minutes with 16 jobs for E1 and E2):

       ./run_gt.sh manifest.tsv gt-work gt_E.tsv 16
       ./run_gt.sh C/manifest.tsv gt-work-C gt_C.tsv 16

4. Run fastppa and report:

       ./evaluate.py run manifest.tsv est_E.tsv \
         --model 'current|../../src/fastppa/fastppa|Reg-to-reg delay|'
       ./evaluate.py report est_E.tsv gt_E.tsv --set E1 \
         --g2 logikbench/results/syn/asic/yosys_freepdk45.json

   Give `--model` more than once to compare several binaries or options on
   the same designs. `--detail` lists the numbers for each design.

## Files

- `make_manifest.py`: lists the designs of E1 and E2, with their top
  module, sources, include directories and defines.
- `gen_microbench.py`: writes the single-operator designs of C.
- `gt_flow.sh`: synthesizes and times one design; runs in the container.
- `run_gt.sh`: runs `gt_flow.sh` over a manifest, in parallel, in one
  container.
- `evaluate.py`: runs fastppa over a manifest, and computes the metrics.
