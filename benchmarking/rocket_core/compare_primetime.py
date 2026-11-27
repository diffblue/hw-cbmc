#!/usr/bin/env python3
"""Compare fastppa estimates against the Synopsys PrimeTime post-route
reports for the Rocket core published by RTL-Timer (see primetime/NOTICE
for provenance and primetime/fetch_reports.sh for upstream verification).

Every number in src/fastppa/COMPARISON.md is produced by this script:

    $ ./compare_primetime.py

Prerequisite: a built fastppa binary (default ../../src/fastppa/fastppa,
override with --fastppa or $FASTPPA).
"""

import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PT_DIR = os.path.join(HERE, "primetime")
RTL = os.path.join(HERE, "rocket_full.v")

# PrimeTime hierarchical instance -> Verilog module in rocket_full.v
MODULES = [
    ("csr", "CSRFile"),
    ("div", "MulDiv"),
    ("ibuf", "IBuf"),
    ("alu", "ALU"),
    ("bpu", "BreakpointUnit"),
]


def read(name):
    with open(os.path.join(PT_DIR, name)) as f:
        return f.read()


def parse_pt_total_area():
    # Rocket.total_area.rpt: "Total  26391 (100%)  42014.97 (100%)"
    m = re.search(
        r"^Total\s+\d+\s+\(100%\)\s+([0-9.]+)\s+\(100%\)",
        read("Rocket.total_area.rpt"),
        re.M)
    assert m, "total area not found in Rocket.total_area.rpt"
    return float(m.group(1))


def parse_pt_critical_path():
    # Rocket.qor.rpt, "Timing Path Group 'CLK_clock' (max_delay/setup)":
    # Levels of Logic and Critical Path Length (ns).
    m = re.search(
        r"Timing Path Group 'CLK_clock' \(max_delay/setup\)\s*\n"
        r"\s*-+\s*\n"
        r"\s*Levels of Logic:\s*([0-9]+)\s*\n"
        r"\s*Critical Path Length:\s*([0-9.]+)",
        read("Rocket.qor.rpt"))
    assert m, "CLK_clock max_delay group not found in Rocket.qor.rpt"
    return float(m.group(2)), int(m.group(1))


def parse_pt_total_power():
    # Rocket.report_power.rpt: "Total Power  =  0.1514 (100.00%)" [W]
    m = re.search(
        r"^Total Power\s*=\s*([0-9.eE+-]+)", read("Rocket.report_power.rpt"),
        re.M)
    assert m, "total power not found in Rocket.report_power.rpt"
    return float(m.group(1)) * 1000.0  # W -> mW


def parse_pt_modules():
    # Rocket.hier_cell_area.txt: extracted 'h' rows of the per-cell
    # power/area report. Tokens: cell, internal, switching, leakage,
    # total power [W], (%), area [um2], 'h'. The (%) field may split
    # into two tokens, so index from both ends.
    out = {}
    for line in read("Rocket.hier_cell_area.txt").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        tok = line.split()
        assert tok[-1] == "h", line
        out[tok[0]] = {
            "power_mw": float(tok[4]) * 1000.0,
            "area_um2": float(tok[-2]),
        }
    return out


def run_fastppa(binary, top):
    result = subprocess.run(
        [binary, RTL, "--top", top, "--process", "45nm"],
        capture_output=True, text=True)
    if result.returncode != 0:
        sys.exit(
            f"fastppa failed on --top {top}:\n{result.stdout}{result.stderr}")
    out = result.stdout

    def grab(pattern):
        m = re.search(pattern, out, re.M)
        assert m, f"pattern {pattern!r} not found in fastppa output for {top}"
        return float(m.group(1))

    return {
        # the "Total:" under "Area:" carries a um2 unit, the one under
        # "Power" carries mW, so the unit disambiguates them
        "area_um2": grab(r"^\s*Total:\s+([0-9.]+) um2"),
        "delay_ns": grab(r"^\s*Reg-to-reg delay:.*\(([0-9.]+) ns\)"),
        "power_mw": grab(r"^\s*Total:\s+([0-9.]+) mW"),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--fastppa",
        default=os.environ.get(
            "FASTPPA",
            os.path.join(HERE, "..", "..", "src", "fastppa", "fastppa")))
    args = ap.parse_args()

    pt_area = parse_pt_total_area()
    pt_delay_ns, pt_levels = parse_pt_critical_path()
    pt_power_mw = parse_pt_total_power()
    pt_modules = parse_pt_modules()

    fp = {top: run_fastppa(args.fastppa, top)
          for top in ["Rocket"] + [m for _, m in MODULES]}

    print("Core (whole design, `--top Rocket`)")
    print()
    print("| quantity | PrimeTime (post-route) | fastppa | ratio |")
    print("|----------|-----------------------|---------|-------|")
    r = fp["Rocket"]
    print(f"| cell area (µm²) | {pt_area:.2f} | {r['area_um2']:.1f} "
          f"| {r['area_um2'] / pt_area:.2f} |")
    print(f"| critical path (ns) | {pt_delay_ns:.3f} "
          f"({pt_levels} levels of logic) | {r['delay_ns']:.3f} "
          f"| {r['delay_ns'] / pt_delay_ns:.2f} |")
    print()

    print("Per-module cell area")
    print()
    print("| instance | module | PrimeTime (µm²) | fastppa (µm²) | ratio |")
    print("|----------|--------|-----------------|---------------|-------|")
    for inst, mod in MODULES:
        pt = pt_modules[inst]["area_um2"]
        est = fp[mod]["area_um2"]
        print(f"| {inst} | {mod} | {pt:.1f} | {est:.1f} | {est / pt:.2f} |")
    print()

    print("Per-module power share (of the five-module subtotal)")
    print()
    print("| instance | module | PrimeTime (mW) | PT share | "
          "fastppa (mW) | fastppa share |")
    print("|----------|--------|----------------|----------|"
          "--------------|---------------|")
    pt_sum = sum(pt_modules[i]["power_mw"] for i, _ in MODULES)
    fp_sum = sum(fp[m]["power_mw"] for _, m in MODULES)
    for inst, mod in MODULES:
        pt = pt_modules[inst]["power_mw"]
        est = fp[mod]["power_mw"]
        print(f"| {inst} | {mod} | {pt:.2f} | {pt / pt_sum:.1%} "
              f"| {est:.1f} | {est / fp_sum:.1%} |")
    print()
    print(f"(PrimeTime total power, whole core: {pt_power_mw:.1f} mW; "
          f"see COMPARISON.md for why absolute power is not comparable.)")


if __name__ == "__main__":
    main()
