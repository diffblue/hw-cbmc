#!/usr/bin/env python3
"""Run fastppa over a manifest and compare its estimates with ground truth.

Usage:
  evaluate.py run <manifest.tsv> <out.tsv> --model SPEC [--model SPEC ...]
                  [--jobs N]
  evaluate.py report <estimates.tsv> <gt.tsv> [--g2 <logikbench json>]
                  [--set S] [--detail]

A model SPEC is 'name|binary|delay label|extra arguments', e.g.
  'current|src/fastppa/fastppa|Reg-to-reg delay|'
The delay label names the line of fastppa's output that holds the delay
in ps. Several models (e.g., two fastppa binaries) can be compared.

'run' writes, per design and model, the total area (um2) and the delay
(ps), or the reason the model failed. 'report' prints the metrics of
PROTOCOL.md over the designs that all models and the ground truth handle.
"""

import argparse
import concurrent.futures
import json
import math
import re
import resource
import subprocess


def limit_memory():
    # 4 GiB address space per fastppa process
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))


def parse_model(spec):
    parts = spec.split("|")
    if len(parts) != 4:
        raise argparse.ArgumentTypeError(f"bad model spec: {spec}")
    name, binary, delay_label, args = parts
    return {"name": name, "binary": binary, "delay": delay_label,
            "args": args.split()}


def run_one(model, row):
    s, name, top, sources, incdirs, defines = row[:6]
    cmd = [model["binary"]] + sources.split() + ["--top", top,
                                                 "--process", "45nm"]
    for i in incdirs.split():
        cmd += ["-I", i]
    for d in defines.split():
        cmd += ["-D", d]
    cmd += model["args"]
    m = model["name"]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=120,
                           preexec_fn=limit_memory)
    except subprocess.TimeoutExpired:
        return (s, name, m, "timeout", "", "")
    out = p.stdout + p.stderr
    if p.returncode != 0:
        err = [l for l in out.splitlines() if "error" in l.lower()]
        reason = (err[-1] if err else f"exit {p.returncode}")[:200]
        return (s, name, m, "failed: " + reason.replace("\t", " "), "", "")
    area = re.search(r"^Area:\n\s+Total:\s+([0-9.]+)", out, re.M)
    delay = re.search(re.escape(model["delay"]) + r":\s+([0-9.]+) ps", out)
    if not area or not delay:
        return (s, name, m, "failed: no result in output", "", "")
    return (s, name, m, "ok", area.group(1), delay.group(1))


def cmd_run(args):
    rows = [l.rstrip("\n").split("\t") for l in open(args.manifest)]
    rows = [r for r in rows if r[2] and not (len(r) > 6 and r[6])]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        futs = [ex.submit(run_one, m, r) for r in rows for m in args.model]
        results = sorted(f.result() for f in futs)
    with open(args.out, "w") as f:
        for r in results:
            f.write("\t".join(r) + "\n")


def geomean(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def quantile(xs, q):
    xs = sorted(xs)
    i = q * (len(xs) - 1)
    lo, hi = math.floor(i), math.ceil(i)
    return xs[lo] + (xs[hi] - xs[lo]) * (i - lo)


def spearman(xs, ys):
    def ranks(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(v):
            j = i
            while j + 1 < len(v) and v[order[j + 1]] == v[order[i]]:
                j += 1
            for k in range(i, j + 1):
                r[order[k]] = (i + j) / 2.0
            i = j + 1
        return r
    rx, ry = ranks(xs), ranks(ys)
    mx, my = sum(rx) / len(rx), sum(ry) / len(ry)
    cov = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    vx = math.sqrt(sum((a - mx) ** 2 for a in rx))
    vy = math.sqrt(sum((b - my) ** 2 for b in ry))
    return cov / (vx * vy) if vx and vy else float("nan")


def metrics(est, truth):
    pairs = [(e, t) for e, t in zip(est, truth) if e > 0 and t > 0]
    zero = len(est) - len(pairs)
    if not pairs:
        return None
    r = [e / t for e, t in pairs]
    err = [max(x, 1 / x) for x in r]
    return {
        "n": len(pairs), "zero": zero, "geomean": geomean(r),
        "median_err": quantile(err, 0.5), "p90_err": quantile(err, 0.9),
        "within1.5": sum(e <= 1.5 for e in err) / len(err),
        "within2": sum(e <= 2 for e in err) / len(err),
        "spearman": spearman([e for e, _ in pairs], [t for _, t in pairs]),
    }


def num(x, scale=1.0):
    return float(x) * scale if x else float("nan")


def cmd_report(args):
    est, models = {}, []
    for l in open(args.estimates):
        s, name, model, status, area, delay = l.rstrip("\n").split("\t")
        if model not in models:
            models.append(model)
        if args.set and s != args.set:
            continue
        est.setdefault(name, {})[model] = (status, area, delay)
    gt = {}
    for l in open(args.gt):
        f = l.rstrip("\n").split("\t")
        gt[f[0]] = f
    g2_area, g2_fmax = {}, {}
    if args.g2:
        m = json.load(open(args.g2))["metrics"]
        for group, v in m["cellarea"].items():
            for b, a in v.items():
                g2_area[f"{group}/{b}"] = a
        for group, v in m["fmax"].items():
            for b, a in v.items():
                g2_fmax[f"{group}/{b}"] = a

    names = sorted(est)
    excluded, common = [], []
    for n in names:
        reasons = []
        for m in models:
            st = est[n].get(m, ("missing",))[0]
            if st != "ok":
                reasons.append(f"{m}: {st}")
        g = gt.get(n)
        if not g or g[1] != "ok":
            reasons.append(f"ground truth: {g[1] if g else 'missing'}")
        (excluded.append((n, "; ".join(reasons))) if reasons
         else common.append(n))

    print(f"designs: {len(names)}, compared: {len(common)}, "
          f"excluded: {len(excluded)}")
    for m in models:
        ok = sum(est[n].get(m, ("",))[0] == "ok" for n in names)
        print(f"  {m} handles {ok}/{len(names)}")

    def table(title, truth_of, field):
        print(f"\n{title}")
        print(f"  {'model':10s} {'n':>4s} {'zero':>4s} {'geomean':>8s} "
              f"{'med.err':>8s} {'p90.err':>8s} {'<=1.5x':>7s} {'<=2x':>6s} "
              f"{'rho':>6s}")
        for m in models:
            ns = [n for n in common if truth_of(n) is not None]
            r = metrics([float(est[n][m][field]) for n in ns],
                        [truth_of(n) for n in ns])
            if r is None:
                print(f"  {m:10s} no data")
                continue
            print(f"  {m:10s} {r['n']:4d} {r['zero']:4d} {r['geomean']:8.2f} "
                  f"{r['median_err']:8.2f} {r['p90_err']:8.2f} "
                  f"{r['within1.5']:7.0%} {r['within2']:6.0%} "
                  f"{r['spearman']:6.2f}")

    table("Area vs G1 (Yosys+ABC, NanGate45)",
          lambda n: float(gt[n][2]) if gt[n][2] else None, 1)
    table("Delay vs G1 (OpenSTA data arrival)",
          lambda n: float(gt[n][3]) * 1000 if gt[n][3] else None, 2)
    if args.g2:
        table("Area vs G2 (LogikBench yosys_freepdk45)",
              lambda n: g2_area.get(n), 1)
        table("Delay vs G2 (1/fmax)",
              lambda n: 1e6 / g2_fmax[n] if g2_fmax.get(n) else None, 2)

    if args.detail:
        print("\nPer design: G1 area, " + ", ".join(models) +
              " | G1 delay, " + ", ".join(models))
        for n in common:
            areas = " ".join(f"{num(est[n][m][1]):10.1f}" for m in models)
            delays = " ".join(f"{num(est[n][m][2]):8.0f}" for m in models)
            print(f"  {n:34s} {num(gt[n][2]):10.1f} {areas} | "
                  f"{num(gt[n][3], 1000):8.0f} {delays}")
    print("\nExcluded:")
    for n, why in excluded:
        print(f"  {n}: {why}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="command", required=True)
    r = sub.add_parser("run")
    r.add_argument("manifest")
    r.add_argument("out")
    r.add_argument("--model", type=parse_model, action="append",
                   required=True)
    r.add_argument("--jobs", type=int, default=16)
    p = sub.add_parser("report")
    p.add_argument("estimates")
    p.add_argument("gt")
    p.add_argument("--g2")
    p.add_argument("--set")
    p.add_argument("--detail", action="store_true")
    args = ap.parse_args()
    (cmd_run if args.command == "run" else cmd_report)(args)


if __name__ == "__main__":
    main()
