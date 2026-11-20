#!/usr/bin/env python3
"""Collect the AIG statistics of fastppa --netlist for a manifest.

The statistics (AND gates, latches and levels in the cone of influence of
the outputs) do not depend on the cell library; fit.py uses them to fit
the cost of an AND gate.

Usage: netlist_counts.py <manifest.tsv> <fastppa> <out.tsv>
Output columns: name, AND gates, latches, levels.
"""

import concurrent.futures
import re
import resource
import subprocess
import sys


def limit_memory():
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))


def run(fastppa, row):
    s, name, top, sources, incdirs, defines = row[:6]
    cmd = [fastppa] + sources.split() + ["--top", top, "--netlist"]
    for i in incdirs.split():
        cmd += ["-I", i]
    for d in defines.split():
        cmd += ["-D", d]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                           preexec_fn=limit_memory)
    except subprocess.TimeoutExpired:
        return None
    m = re.search(r"Netlist: (\d+) AND gates, (\d+) latches, (\d+) levels",
                  p.stdout + p.stderr)
    return (name,) + m.groups() if m else None


def main():
    manifest, fastppa, out = sys.argv[1:4]
    rows = [l.rstrip("\n").split("\t") for l in open(manifest)]
    rows = [r for r in rows if r[2] and not (len(r) > 6 and r[6])]
    with concurrent.futures.ThreadPoolExecutor(16) as ex:
        results = [r for r in ex.map(lambda r: run(fastppa, r), rows) if r]
    with open(out, "w") as f:
        for r in sorted(results):
            f.write("\t".join(r) + "\n")


if __name__ == "__main__":
    main()
