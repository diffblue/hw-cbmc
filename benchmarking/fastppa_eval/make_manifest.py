#!/usr/bin/env python3
"""Write a manifest of designs for the fastppa evaluation.

Each line of the manifest is tab-separated:
  set  name  top  sources  incdirs  defines
with space-separated lists. Sets:
  E1  LogikBench groups basic, arithmetic, memory, blocks (see PROTOCOL.md)
  E2  regression/fastppa/{blocks,designs} of PR #1927

Usage: make_manifest.py --logikbench <dir> --lambdalib <dir> --repo <dir> out.tsv
"""

import argparse
import re
import sys
from pathlib import Path

E1_GROUPS = ["basic", "arithmetic", "memory", "blocks"]


def load_resolver(repo):
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(Path(repo) / "benchmarking"))
    import logikbench_resolve_fileset as r
    return r


def logikbench_designs(r, lb_root, ll_root):
    r.install_stubs()
    sys.path.insert(0, str(Path(lb_root).resolve()))
    sys.path.insert(0, str(Path(ll_root).resolve()))

    # Capture the top module of the 'rtl' fileset.
    tops = {}

    def set_topmodule(self, top, fileset=None, *args, **kwargs):
        if fileset is None and self._fileset_stack:
            fileset = self._fileset_stack[-1]
        if fileset in (None, "rtl"):
            tops[id(self)] = top

    r.Design.set_topmodule = set_topmodule

    bench_root = Path(lb_root) / "logikbench" / "benchmarks"
    for group in E1_GROUPS:
        for bench in sorted((bench_root / group).iterdir()):
            py = bench / f"{bench.name}.py"
            if not (bench / "rtl").is_dir() or not py.is_file():
                continue
            try:
                design = r.load_design_class(py.resolve())()
                files, idirs, defines = r.collect_fileset(design, "rtl")
            except Exception as e:  # recorded, not silently dropped
                yield ("E1", f"{group}/{bench.name}", "", [], [], [],
                       f"resolve: {e}")
                continue
            idirs = r.ordered_unique(idirs + [f.parent for f in files])
            top = tops.get(id(design), bench.name)
            yield ("E1", f"{group}/{bench.name}", top, files, idirs, defines,
                   "")


def regression_designs(repo):
    reg = Path(repo).resolve() / "regression" / "fastppa"
    for sub in ["blocks", "designs"]:
        for desc in sorted((reg / sub).glob("*.desc")):
            lines = desc.read_text().splitlines()
            if len(lines) < 3:
                continue
            src = reg / sub / lines[1].strip()
            m = re.search(r"--top\s+(\S+)", lines[2])
            if not m or not src.is_file():
                continue
            yield ("E2", f"{sub}/{src.stem}", m.group(1), [src], [src.parent],
                   [], "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--logikbench", required=True)
    ap.add_argument("--lambdalib", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("out")
    args = ap.parse_args()

    r = load_resolver(args.repo)
    rows, seen = [], set()
    for row in list(logikbench_designs(r, args.logikbench, args.lambdalib)) + \
            list(regression_designs(args.repo)):
        if (row[0], row[1]) in seen:
            continue  # several .desc files per design
        seen.add((row[0], row[1]))
        rows.append(row)

    with open(args.out, "w") as out:
        for s, name, top, files, idirs, defines, err in rows:
            out.write("\t".join([s, name, top,
                                 " ".join(str(f) for f in files),
                                 " ".join(str(d) for d in idirs),
                                 " ".join(defines), err]) + "\n")
    print(f"{len(rows)} designs", file=sys.stderr)


if __name__ == "__main__":
    main()
