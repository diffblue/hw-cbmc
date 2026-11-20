#!/usr/bin/env python3
"""Generate the calibration set C of per-operator microbenchmarks.

Each microbenchmark contains a single operator (or a register, or an array
access), so that its synthesized area and delay can be attributed to that
operator. Writes <outdir>/<name>.sv and <outdir>/manifest.tsv (in the format
of make_manifest.py, with set C), plus <outdir>/params.tsv with the
parameters (kind, width, size) of each microbenchmark.
"""

import math
import sys
from pathlib import Path

WIDTHS = [4, 8, 16, 32, 64]

BINARY = {
    "plus": "a + b", "minus": "a - b",
    "bitand": "a & b", "bitor": "a | b", "bitxor": "a ^ b",
}
BINARY_NARROW = {"mult": "a * b", "div": "a / b", "mod": "a % b"}
UNARY = {"bitnot": "~a", "unary_minus": "-a"}
COMPARE = {"equal": "a == b", "lt": "a < b"}
REDUCE = {"reduction_and": "&a", "reduction_or": "|a", "reduction_xor": "^a"}
SHIFT = {"shl": "a << s", "lshr": "a >> s", "ashr": "$signed(a) >>> s"}


def emit(out, name, text, params, rows):
    (out / f"{name}.sv").write_text(text)
    rows.append((name, params))


def main():
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    rows = []

    for op, e in BINARY.items():
        for w in WIDTHS:
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, b, output [{w-1}:0] y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    for op, e in BINARY_NARROW.items():
        for w in [4, 8, 16, 32]:
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, b, output [{w-1}:0] y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    for op, e in UNARY.items():
        for w in WIDTHS:
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, output [{w-1}:0] y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    for op, e in COMPARE.items():
        for w in WIDTHS:
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, b, output y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    for op, e in REDUCE.items():
        for w in WIDTHS:
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, output y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    for op, e in SHIFT.items():
        for w in WIDTHS:
            sw = max(1, math.ceil(math.log2(w)))
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, input [{sw-1}:0] s,"
                 f" output [{w-1}:0] y);\n"
                 f"  assign y = {e};\nendmodule\n", (op, w, 0), rows)
    # operators with a constant operand; the constant has every other bit
    # set, starting with the least significant one
    def k(w):
        return int("01" * w, 2) & ((1 << w) - 1) | 1
    for op, e in {"plus_c": "a + K", "equal_c": "a == K",
                  "lt_c": "a < K"}.items():
        for w in WIDTHS:
            yw = 1 if op != "plus_c" else w
            emit(out, f"{op}_{w}",
                 f"module {op}_{w}(input [{w-1}:0] a, output [{yw-1}:0] y);\n"
                 f"  assign y = {e.replace('K', f'{w}\'d{k(w)}')};\n"
                 f"endmodule\n", (op, w, 0), rows)
    for w in [4, 8, 16, 32]:
        emit(out, f"mult_c_{w}",
             f"module mult_c_{w}(input [{w-1}:0] a, output [{w-1}:0] y);\n"
             f"  assign y = a * {w}'d{k(w)};\nendmodule\n",
             ("mult_c", w, 0), rows)
    for w in WIDTHS:
        emit(out, f"mux_{w}",
             f"module mux_{w}(input s, input [{w-1}:0] a, b,"
             f" output [{w-1}:0] y);\n"
             f"  assign y = s ? a : b;\nendmodule\n", ("if", w, 0), rows)
    for w in WIDTHS:
        emit(out, f"reg_{w}",
             f"module reg_{w}(input clk, input [{w-1}:0] d,"
             f" output reg [{w-1}:0] q);\n"
             f"  always @(posedge clk) q <= d;\nendmodule\n",
             ("register", w, 0), rows)
    # array read with a variable index, from an array of wires
    for w in [1, 8, 32]:
        for n in [4, 8, 16, 32, 64]:
            iw = max(1, math.ceil(math.log2(n)))
            emit(out, f"index_{w}_{n}",
                 f"module index_{w}_{n}(input [{n*w-1}:0] flat,"
                 f" input [{iw-1}:0] i, output [{w-1}:0] y);\n"
                 f"  wire [{w-1}:0] m [0:{n-1}];\n"
                 f"  for(genvar g = 0; g < {n}; g++) begin : G\n"
                 f"    assign m[g] = flat[g*{w} +: {w}];\n  end\n"
                 f"  assign y = m[i];\nendmodule\n", ("index", w, n), rows)
    # array write with a variable index, into an array of registers
    for w in [8, 32]:
        for n in [4, 8, 16, 32]:
            iw = max(1, math.ceil(math.log2(n)))
            emit(out, f"with_{w}_{n}",
                 f"module with_{w}_{n}(input clk, input [{iw-1}:0] i,"
                 f" input [{w-1}:0] d, output [{n*w-1}:0] flat);\n"
                 f"  reg [{w-1}:0] m [0:{n-1}];\n"
                 f"  always @(posedge clk) m[i] <= d;\n"
                 f"  for(genvar g = 0; g < {n}; g++) begin : G\n"
                 f"    assign flat[g*{w} +: {w}] = m[g];\n  end\nendmodule\n",
                 ("with", w, n), rows)

    with open(out / "manifest.tsv", "w") as m, open(out / "params.tsv", "w") as p:
        for name, (kind, w, n) in rows:
            m.write("\t".join(["C", name, name, str((out / f"{name}.sv").resolve()),
                               "", "", ""]) + "\n")
            p.write(f"{name}\t{kind}\t{w}\t{n}\n")
    print(f"{len(rows)} microbenchmarks", file=sys.stderr)


if __name__ == "__main__":
    main()
