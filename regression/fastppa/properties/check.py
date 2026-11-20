#!/usr/bin/env python3
"""Property tests for fastppa.

Instead of pinning estimated values, these tests check properties that
any correct estimate has, and that the estimates stay within a tolerance
of synthesis results:

- invariance: designs that describe the same hardware get the same
  estimate (re-association, named wires, renaming, shared logic, logic
  that reaches no output);
- monotonicity: wider operators cost more, and older nodes have larger
  cells;
- tolerance: over the designs in reference.tsv, the estimates are within
  given error factors of synthesis (Yosys+ABC with NanGate45, OpenSTA).

Usage: check.py <fastppa>
"""

import math
import os
import re
import resource
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FASTPPA = os.path.abspath(sys.argv[1])
failures = []


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))


def estimate(path, top="main", args=()):
    p = subprocess.run([FASTPPA, path, "--top", top] + list(args),
                       capture_output=True, text=True, timeout=120,
                       preexec_fn=limit)
    out = p.stdout + p.stderr
    if p.returncode != 0:
        raise RuntimeError(f"{path} {' '.join(args)}: exit {p.returncode}\n"
                           f"{out}")

    def num(pattern):
        m = re.search(pattern, out, re.M)
        return float(m.group(1)) if m else None
    return {
        "area": num(r"^Area:\n\s+Total:\s+([0-9.]+)"),
        "delay": num(r"Critical path:\s+([0-9.]+) ps"),
        "power": num(r"^Power.*\n(?:.*\n)*?\s+Total:\s+([0-9.]+) mW"),
    }


def check(condition, message):
    print(("ok    " if condition else "FAIL  ") + message)
    if not condition:
        failures.append(message)


def design(name):
    return os.path.join(HERE, name + ".sv")


MODES = [("graph", []), ("netlist", ["--netlist"])]

for mode, args in MODES:
    all_quantities = ["area", "delay", "power"]
    groups = [
        ("named wires, renaming",
         ["chain_nested", "chain_wires", "chain_renamed"], all_quantities),
        # The AIG is not rebalanced, so --netlist only keeps the area.
        ("re-association", ["chain_nested", "chain_balanced"],
         all_quantities if mode == "graph" else ["area", "power"]),
        ("a product used by two registers", ["share_one", "share_two"],
         all_quantities),
        ("a register that reaches no output", ["dead_none", "dead_extra"],
         all_quantities),
    ]
    for what, names, quantities in groups:
        estimates = [estimate(design(n), args=args) for n in names]
        same = all(e[q] == estimates[0][q] for e in estimates
                   for q in quantities)
        check(same, f"{mode}: same {', '.join(quantities)} for {what}")

    for op in ["add", "mult"]:
        ests = [estimate(design(f"{op}_{w}"), args=args)
                for w in [8, 16, 32, 64]]
        for q in ["area", "power"]:
            values = [e[q] for e in ests]
            check(all(a < b for a, b in zip(values, values[1:])),
                  f"{mode}: {op} {q} grows with width {values}")
        delays = [e["delay"] for e in ests]
        check(all(a <= b for a, b in zip(delays, delays[1:])),
              f"{mode}: {op} delay does not shrink with width {delays}")

areas = [estimate(design("mult_32"), args=["--process", p])["area"]
         for p in ["180nm", "130nm", "45nm", "28nm", "7nm", "3nm"]]
check(all(a > b for a, b in zip(areas, areas[1:])),
      f"area shrinks from 180nm to 3nm {areas}")

# Tolerance against synthesis. reference.tsv: design, top, area (um2),
# delay (ns), from benchmarking/fastppa_eval/results/gt_E.tsv.
LIMITS = {
    # mode: quantity -> (largest median error, smallest share within 2x)
    "graph": {"area": (1.5, 0.75), "delay": (1.5, 0.70)},
    "netlist": {"area": (1.5, 0.80)},
}
reference = []
for line in open(os.path.join(HERE, "reference.tsv")):
    if line.startswith("#") or not line.strip():
        continue
    path, top, area, delay = line.split()
    reference.append((path, top, float(area), float(delay) * 1000))

for mode, args in MODES:
    errors = {"area": [], "delay": []}
    for path, top, area, delay in reference:
        e = estimate(os.path.join(HERE, "..", path), top, args)
        for q, truth in [("area", area), ("delay", delay)]:
            if truth > 0 and e[q] and e[q] > 0:
                r = e[q] / truth
                errors[q].append(max(r, 1 / r))
    for q, (max_median, min_within2) in LIMITS[mode].items():
        errs = sorted(errors[q])
        median = errs[len(errs) // 2]
        within2 = sum(x <= 2 for x in errs) / len(errs)
        check(median <= max_median and within2 >= min_within2,
              f"{mode}: {q} on {len(errs)} designs: median error "
              f"{median:.2f}x (at most {max_median}x), within 2x "
              f"{within2:.0%} (at least {min_within2:.0%})")

if failures:
    print(f"\n{len(failures)} property checks failed")
    sys.exit(1)
print("\nAll property checks passed")
