#!/usr/bin/env python3
"""Derive cost tables for nodes without an open cell library.

A derived table is a measured table with all areas, delays and energies
multiplied by published scaling factors; leakage is scaled like area.
See PROCESS_NODES.md for the sources of the factors.

Usage: derive.py <anchor.inc> <node> <out.inc>
"""

import sys

# DeepScaleTool (Sarangi and Baas, ISCAS 2021), spreadsheet of 03/02/2021:
# area, delay and energy relative to the tool's reference node.
DEEPSCALETOOL = {
    "130nm": (8.3, 1.96, 2.52),
    "90nm": (3.94, 1.31, 1.51),
    "65nm": (2.04, 1.0, 1.0),
    "45nm": (1.0, 0.81, 0.63),
    "28nm": (0.35, 0.67, 0.37),
    "14nm": (0.08, 0.60, 0.19),
    "7nm": (0.011, 0.53, 0.11),
}

# TSMC N7 -> N5: 1.8x logic density, +15% speed, -30% power;
# N5 -> N3: 1.6x logic density, +10-15% speed, -25-30% power.
TSMC_FROM_7NM = {
    "5nm": (1 / 1.8, 1 / 1.15, 0.70),
    "3nm": (1 / 1.8 / 1.6, 1 / 1.15 / 1.125, 0.70 * 0.725),
}

ANCHOR = {**{n: ("nangate45", "45nm") for n in DEEPSCALETOOL},
          **{n: ("asap7", None) for n in TSMC_FROM_7NM}}


def factors(node):
    """(area, delay, energy) factors from the anchor table to node."""
    if node in TSMC_FROM_7NM:
        return TSMC_FROM_7NM[node]
    a, d, e = DEEPSCALETOOL[node]
    a0, d0, e0 = DEEPSCALETOOL["45nm"]
    return (a / a0, d / d0, e / e0)


def main():
    anchor_file, node, out_file = sys.argv[1:4]
    fa, fd, fe = factors(node)
    lines = open(anchor_file).read().splitlines()
    out = [f"// Derived by benchmarking/fastppa_eval/derive.py for {node} "
           f"from the {ANCHOR[node][0]} table; do not edit.",
           f"R\"(# area x{fa:.6g}, delay x{fd:.6g}, energy x{fe:.6g}, "
           f"leakage x{fa:.6g}"]
    for line in lines:
        if line.startswith("//") or line.startswith("R\"(") or \
                line.startswith(")\"") or line.startswith("#"):
            if line.startswith("R\"(#"):
                out.append(line[3:])
            elif line.startswith("#"):
                out.append(line)
            continue
        k, af, a0, a1, df, d0, d1, e0, e1, l0, l1 = line.split()
        v = [float(x) for x in (a0, a1, d0, d1, e0, e1, l0, l1)]
        v = [v[0] * fa, v[1] * fa, v[2] * fd, v[3] * fd,
             v[4] * fe, v[5] * fe, v[6] * fa, v[7] * fa]
        out.append(f"{k} {af} {v[0]:.6g} {v[1]:.6g} {df} {v[2]:.6g} "
                   f"{v[3]:.6g} {v[4]:.6g} {v[5]:.6g} {v[6]:.6g} {v[7]:.6g}")
    out.append(")\"")
    open(out_file, "w").write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
