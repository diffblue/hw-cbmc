#!/usr/bin/env python3
"""Fit the cost table of the graph estimator on the calibration set C.

Inputs: params.tsv from gen_microbench.py and the ground truth of C from
run_gt.sh for one cell library. Output: a cost table for that library.

For every operator kind, area = a0 + a1*F and delay = d0 + d1*G, with
F and G taken from a small set of candidate forms for that kind. The
data energy per cycle (per unit of input activity) and the leakage power
are fitted with the form of the area. The clock energy per register bit
is fitted separately. The
coefficients minimise the squared relative error (non-negative least
squares); the form is the one with the smallest leave-one-out error, so
only the data of C is used to choose it.

Usage: fit.py <params.tsv> <gt_C.tsv> <netlist_counts.tsv> <cost_table.inc>
              [report.txt]

netlist_counts.tsv (from netlist_counts.py) gives the AIG of every
calibration design, from which the cost of one AND gate ('aig_and') is
fitted: area, energy and leakage per gate, and delay per level.

The output is a C++ raw string literal, which src/fastppa/cost_table.cpp
includes; the text inside it can also be given to fastppa --cost-table.
"""

import math
import sys

import numpy as np
from scipy.optimize import nnls

# kind -> (area forms, delay forms)
LINEAR = (["w"], ["1", "logw", "w"])
CANDIDATES = {
    "plus": (["w", "wlogw"], ["logw", "w"]),
    "minus": (["w", "wlogw"], ["logw", "w"]),
    "plus_c": (["w", "wlogw"], ["logw", "w"]),
    "unary_minus": (["w", "wlogw"], ["logw", "w"]),
    "mult": (["w2", "wlogw"], ["logw", "w"]),
    "mult_c": (["w2", "wlogw", "w"], ["logw", "w"]),
    "div": (["w2"], ["w", "w2"]),
    "mod": (["w2"], ["w", "w2"]),
    "bitand": (["w"], ["1"]),
    "bitor": (["w"], ["1"]),
    "bitxor": (["w"], ["1"]),
    "bitnot": (["w"], ["1"]),
    "equal": LINEAR, "equal_c": LINEAR, "lt": LINEAR, "lt_c": LINEAR,
    "reduction_and": LINEAR, "reduction_or": LINEAR,
    "reduction_xor": LINEAR,
    "shl": (["w", "wlogw"], ["logw", "w"]),
    "lshr": (["w", "wlogw"], ["logw", "w"]),
    "ashr": (["w", "wlogw"], ["logw", "w"]),
    "if": (["w"], ["1"]),
    "register": (["w"], ["1"]),
    "index": (["wn1", "wn"], ["logn", "n"]),
    "with": (["wn", "n"], ["logn", "1"]),
}


def form(f, w, n):
    W, N = max(w, 1), max(n, 1)
    return {"1": 1.0, "w": W, "logw": math.log2(W), "wlogw": W * math.log2(W),
            "w2": W * W, "n": N, "logn": math.log2(N), "wn": W * N,
            "wn1": W * (N - 1)}[f]


def fit(f, xs, ys):
    """Non-negative fit of y = c0 + c1*F(x), minimising relative error."""
    if f == "1":
        # a constant: the geometric mean minimises the mean log error
        return [float(np.exp(np.mean(np.log(ys)))), 0.0]
    A = np.array([[1.0 / y, form(f, w, n) / y] for (w, n), y in zip(xs, ys)])
    c, _ = nnls(A, np.ones(len(ys)))
    return [float(c[0]), float(c[1])]


def predict(f, c, w, n):
    return c[0] + c[1] * (form(f, w, n) if f != "1" else 0.0)


def loo_error(f, xs, ys):
    """Mean |log(prediction/truth)| in leave-one-out cross-validation."""
    if len(ys) < 3:
        return float("inf")
    errs = []
    for i in range(len(ys)):
        c = fit(f, xs[:i] + xs[i + 1:], ys[:i] + ys[i + 1:])
        p = predict(f, c, *xs[i])
        errs.append(abs(math.log(max(p, 1e-9) / ys[i])))
    return float(np.mean(errs))


def choose(forms, xs, ys):
    best = min(forms, key=lambda f: loo_error(f, xs, ys))
    return best, fit(best, xs, ys), loo_error(best, xs, ys)


def main():
    params_file, gt_file, counts_file, out_file = sys.argv[1:5]
    report_file = sys.argv[5] if len(sys.argv) > 5 else None

    params = {}
    for line in open(params_file):
        name, kind, w, n = line.rstrip("\n").split("\t")
        params[name] = (kind, int(w), int(n))
    gt = {}
    for line in open(gt_file):
        f = line.rstrip("\n").split("\t")
        if f[1] == "ok":
            # um2, ps, clock energy fJ, data energy fJ per unit activity,
            # leakage uW
            gt[f[0]] = (float(f[2]), float(f[3]) * 1000.0, float(f[6]),
                        float(f[7]), float(f[8]))
    missing = sorted(set(params) - set(gt))
    if missing:
        sys.exit(f"no ground truth for: {' '.join(missing)}")

    data = {}
    for name, (kind, w, n) in params.items():
        data.setdefault(kind, []).append(((w, n), gt[name]))

    table, report = {}, []

    def fit_values(form, xs, ys):
        """Fit with a given form; values that are not positive are left
        out, and a quantity that is never positive costs nothing."""
        pts = [(x, y) for x, y in zip(xs, ys) if y > 0]
        if len(pts) < 2:
            return [0.0, 0.0]
        return fit(form, [x for x, _ in pts], [y for _, y in pts])

    def fit_kind(kind, subtract=None):
        rows = sorted(data[kind])
        xs = [x for x, _ in rows]
        sub = [subtract(*x) if subtract else (0, 0) for x in xs]
        areas = [g[0] - s[0] for (_, g), s in zip(rows, sub)]
        delays = [g[1] for _, g in rows]
        energies = [g[3] for _, g in rows]
        leakages = [g[4] - s[1] for (_, g), s in zip(rows, sub)]
        af, ac, ae = choose(CANDIDATES[kind][0], xs, areas)
        df, dc, de = choose(CANDIDATES[kind][1], xs, delays)
        ec = fit_values(af, xs, energies)
        lc = fit_values(af, xs, leakages)
        table[kind] = (af, ac, df, dc, ec, lc)
        report.append(f"{kind:14s} area {af:6s} a0={ac[0]:9.3f} a1={ac[1]:9.4f}"
                      f" loo={math.exp(ae):.3f}x   delay {df:5s}"
                      f" d0={dc[0]:8.2f} d1={dc[1]:8.3f}"
                      f" loo={math.exp(de):.3f}x   energy e1={ec[1]:.4g}"
                      f"   leakage l1={lc[1]:.4g}")
        return rows

    rows = fit_kind("register")
    af, ac, _, _, _, lc = table["register"]
    # clock energy per register bit
    cc = fit_values("w", [x for x, _ in rows], [g[2] for _, g in rows])
    table["clock"] = ("w", [0.0, 0.0], "1", [0.0, 0.0], cc, [0.0, 0.0])
    report.append(f"{'clock':14s} energy per bit e0={cc[0]:.4g} e1={cc[1]:.4g}")

    def register_cost(w, n):
        return (predict(af, ac, w * n, 0), predict(af, lc, w * n, 0))

    for kind in CANDIDATES:
        if kind == "register":
            continue
        # the 'with' benchmarks contain the n*w register bits they write to
        fit_kind(kind, register_cost if kind == "with" else None)

    # One AND gate of the AIG: area, energy and leakage per gate after
    # subtracting the registers, delay per level of the combinational
    # designs.
    counts = {}
    for line in open(counts_file):
        name, ands, latches, levels = line.rstrip("\n").split("\t")
        counts[name] = (int(ands), int(latches), int(levels))

    def per_gate(i, register):
        pts = []
        for name, (ands, latches, _) in counts.items():
            if name in gt and ands > 0:
                y = gt[name][i] - latches * register
                if y > 0:
                    pts.append((ands, y))
        if not pts:
            return 0.0
        # minimise the squared relative error of y = c * ands
        return sum(a / y for a, y in pts) / sum((a / y) ** 2 for a, y in pts)

    ra, re_, rl = (predict(af, ac, 1, 0), table["register"][4][1],
                   table["register"][5][1])
    a_and = per_gate(0, ra)
    e_and = per_gate(3, re_)
    l_and = per_gate(4, rl)
    level_pts = [(lv, gt[n][1]) for n, (a, la, lv) in counts.items()
                 if n in gt and la == 0 and lv > 0]
    d_and = sum(l / y for l, y in level_pts) / \
        sum((l / y) ** 2 for l, y in level_pts)
    table["aig_and"] = ("w", [0.0, a_and], "1", [d_and, 0.0], [0.0, e_and],
                        [0.0, l_and])
    report.append(f"{'aig_and':14s} area {a_and:.4g} delay/level {d_and:.4g}"
                  f" energy {e_and:.4g} leakage {l_and:.4g}")

    with open(out_file, "w") as out:
        out.write("// Generated by benchmarking/fastppa_eval/fit.py; "
                  "do not edit.\n"
                  "R\"(# kind area_form a0 a1 delay_form d0 d1 e0 e1 l0 l1\n"
                  "# um2, ps, fJ per cycle per unit of activity, uW;\n"
                  "# energy and leakage have the area form\n")
        for kind, (af, ac, df, dc, ec, lc) in table.items():
            out.write(f"{kind} {af} {ac[0]:.6g} {ac[1]:.6g} "
                      f"{df} {dc[0]:.6g} {dc[1]:.6g} "
                      f"{ec[0]:.6g} {ec[1]:.6g} {lc[0]:.6g} {lc[1]:.6g}\n")
        out.write(")\"\n")
    text = "\n".join(report) + "\n"
    if report_file:
        open(report_file, "w").write(text)
    sys.stdout.write(text)


if __name__ == "__main__":
    main()
