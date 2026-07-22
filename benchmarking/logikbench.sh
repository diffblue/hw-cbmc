#!/bin/sh

# This runs ebmc over the RTL circuits in the LogikBench benchmark suite
# (https://github.com/zeroasiccorp/logikbench) and produces an HTML report.
#
# LogikBench is a large collection of human-authored and AI-generated Verilog
# and SystemVerilog RTL circuits, organised into benchmark groups (basic,
# arithmetic, memory, blocks, epfl, iscas85, iscas89, koios, large).  Each
# benchmark lives in benchmarks/<group>/<name>/ with its RTL under an rtl/
# subdirectory.
#
# For every benchmark, ebmc is asked to parse and elaborate the design
# (--bound 0).  This exercises the Verilog/SystemVerilog front-end and the
# elaboration machinery over a wide range of real-world circuits.  The script
# is a report-only smoke test: it writes a per-circuit HTML report but always
# exits successfully, so that circuits ebmc cannot yet handle (e.g. unsupported
# SystemVerilog constructs or very large SoCs) do not fail CI.
#
# Usage: logikbench.sh [output.html]
#   The report is written to the given path (default: logikbench-report.html).

set -u

# Pin to a known revision for reproducibility.
LOGIKBENCH_REV=main

# Per-circuit wall-clock limit, in seconds, so that a single hard design
# cannot stall the whole run.  Uses coreutils `timeout` (present on Linux) or
# `gtimeout` (coreutils on macOS, `brew install coreutils`).
PER_CIRCUIT_TIMEOUT=${PER_CIRCUIT_TIMEOUT:-60}

# Per-circuit virtual memory limit, in KB, so that a single design whose
# elaboration blows up (e.g. an unrolled loop producing exponentially large
# expressions) cannot exhaust all memory on the machine and take the whole
# run down with it.  Applied via the `ulimit -v` shell builtin, which is not
# available on macOS; the run proceeds without a memory limit there.
PER_CIRCUIT_MEM_KB=${PER_CIRCUIT_MEM_KB:-4000000}

REPORT=${1:-logikbench-report.html}

if command -v timeout > /dev/null 2>&1 ; then
  RUN="timeout $PER_CIRCUIT_TIMEOUT"
elif command -v gtimeout > /dev/null 2>&1 ; then
  RUN="gtimeout $PER_CIRCUIT_TIMEOUT"
else
  echo "warning: no timeout/gtimeout found; running without a per-circuit limit"
  RUN=""
fi

if [ ! -e logikbench/.git ] ; then
  echo "Cloning the LogikBench repository"
  git clone --depth 1 --branch "$LOGIKBENCH_REV" \
    https://github.com/zeroasiccorp/logikbench.git logikbench
fi

BENCHMARKS=logikbench/logikbench/benchmarks

if [ ! -d "$BENCHMARKS" ] ; then
  echo "LogikBench benchmarks directory not found at $BENCHMARKS"
  exit 1
fi

EBMC_VERSION=`ebmc --version 2>/dev/null || echo unknown`
LOGIKBENCH_SHA=`git -C logikbench rev-parse --short HEAD 2>/dev/null || echo unknown`
GENERATED_ON=`date -u '+%Y-%m-%d %H:%M:%S UTC'`

echo "Running ebmc on the LogikBench circuits"
echo

total=0
pass=0
fail=0

# Rows of the report table are accumulated in a temporary file.
ROWS=`mktemp`
trap 'rm -f "$ROWS" logikbench.out' EXIT

# Iterate over the benchmark groups.
for group in "$BENCHMARKS"/*/ ; do
  [ -d "$group" ] || continue
  group_name=`basename "$group"`

  # Iterate over the individual benchmarks in the group.
  for bench in "$group"*/ ; do
    [ -d "${bench}rtl" ] || continue

    # Source files: the Verilog/SystemVerilog under rtl/.  ebmc selects
    # SystemVerilog automatically for the .sv extension.
    sources=`find "${bench}rtl" -name '*.v' -o -name '*.sv' | sort`
    [ -n "$sources" ] || continue

    bench_name=`basename "$bench"`

    # Include directories: rtl/ and, if present, include/, so that `include
    # directives and header (.vh) files resolve.
    incflags="-I ${bench}rtl"
    if [ -d "${bench}include" ] ; then
      incflags="$incflags -I ${bench}include"
    fi

    total=`expr $total + 1`

    # Parse and elaborate only (--bound 0).  Exit code 1 indicates a
    # front-end/elaboration error; 124 is a timeout; anything else means ebmc
    # processed the design (0 = holds/no properties, 10 = counterexample, ...).
    ( ulimit -v $PER_CIRCUIT_MEM_KB 2>/dev/null
      $RUN ebmc $incflags --bound 0 $sources ) > logikbench.out 2>&1
    status=$?

    if [ "$status" = 0 ] || [ "$status" = 10 ] ; then
      echo "  ok      $group_name/$bench_name"
      pass=`expr $pass + 1`
      css=ok ; label=ok
    elif [ "$status" = 124 ] ; then
      echo "  TIMEOUT $group_name/$bench_name"
      fail=`expr $fail + 1`
      css=timeout ; label="timeout"
    else
      echo "  FAIL    $group_name/$bench_name"
      fail=`expr $fail + 1`
      css=fail ; label="fail ($status)"
    fi

    printf '<tr class="%s"><td>%s</td><td>%s</td><td>%s</td></tr>\n' \
      "$css" "$group_name" "$bench_name" "$label" >> "$ROWS"
  done
done

echo
echo "LogikBench summary: $pass/$total circuits elaborated ($fail failed)"

# Emit the HTML report.
{
  cat <<HTML_HEAD
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>EBMC on LogikBench</title>
<style>
  :root { color-scheme: light dark; }
  body { font-family: -apple-system, system-ui, sans-serif; margin: 2rem auto;
         max-width: 60rem; padding: 0 1rem; line-height: 1.5; }
  h1 { margin-bottom: 0.25rem; }
  .meta { color: #666; font-size: 0.9rem; margin-bottom: 1.5rem; }
  .meta code { font-size: 0.85rem; }
  .cards { display: flex; gap: 1rem; margin: 1.5rem 0; flex-wrap: wrap; }
  .card { border: 1px solid #ccc; border-radius: 0.5rem; padding: 0.75rem 1.25rem;
          text-align: center; min-width: 6rem; }
  .card .n { font-size: 1.75rem; font-weight: 600; display: block; }
  table { border-collapse: collapse; width: 100%; }
  th, td { text-align: left; padding: 0.35rem 0.75rem; border-bottom: 1px solid #ddd; }
  th { position: sticky; top: 0; background: Canvas; }
  tr.ok td:last-child { color: #1a7f37; }
  tr.fail td:last-child { color: #cf222e; }
  tr.timeout td:last-child { color: #9a6700; }
</style>
</head>
<body>
<h1>EBMC on LogikBench</h1>
<p class="meta">
  Results of running <a href="https://github.com/diffblue/hw-cbmc">ebmc</a>
  (parse &amp; elaborate, <code>--bound 0</code>) over the
  <a href="https://github.com/zeroasiccorp/logikbench">LogikBench</a>
  RTL benchmark suite.<br>
  Generated $GENERATED_ON &middot;
  ebmc <code>$EBMC_VERSION</code> &middot;
  logikbench <code>$LOGIKBENCH_SHA</code>
</p>
<div class="cards">
  <div class="card"><span class="n">$total</span>circuits</div>
  <div class="card"><span class="n">$pass</span>elaborated</div>
  <div class="card"><span class="n">$fail</span>failed</div>
</div>
<table>
<thead><tr><th>Group</th><th>Circuit</th><th>Result</th></tr></thead>
<tbody>
HTML_HEAD
  cat "$ROWS"
  cat <<'HTML_TAIL'
</tbody>
</table>
</body>
</html>
HTML_TAIL
} > "$REPORT"

echo "Report written to $REPORT"

# Report-only: always succeed, regardless of individual circuit failures.
exit 0
