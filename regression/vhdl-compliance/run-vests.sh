#!/usr/bin/env bash
#
# Runs the parser of the VHDL front-end over the VHDL-93 compliance tests
# of VESTs (Vhdl tESTs, Clifton Labs / University of Cincinnati), as
# distributed with GHDL in testsuite/vests/vhdl-93. The suite is GPL
# licensed and is thus not part of this repository; it is fetched here.
#
# Only parsing is tested, i.e., this measures the acceptance of the
# parser, not compliance: the "compliant" tests should be accepted by the
# parser, and the acceptance rate must not fall below the baseline in
# baseline.txt. The baseline is raised as the grammar grows. For the
# "non_compliant" tests, the number rejected is reported; these are
# mostly semantic errors, which the parser does not detect.
#
# Crashes (signals, invariant violations) and timeouts are counted
# separately, and fail the run.
#
# Usage: run-vests.sh [path/to/ebmc] [report.html]
#   When a report path is given, an HTML report is written to it.

set -eu

EBMC=${1:-$(dirname "$0")/../../src/ebmc/ebmc}
EBMC=$(realpath "$EBMC")
REPORT=${2:-}
BASELINE=$(dirname "$0")/baseline.txt
VESTS_DIR=${VESTS_DIR:-/tmp/ghdl-vests}
VESTS_URL=https://github.com/ghdl/ghdl
# the GHDL commit the suite is taken from, for reproducible results
VESTS_COMMIT=${VESTS_COMMIT:-39bd39022684411317f5903dd8c0723b22e3618f}

if [ ! -d "$VESTS_DIR/testsuite/vests/vhdl-93" ]; then
  git clone --filter=blob:none --sparse --no-checkout "$VESTS_URL" "$VESTS_DIR"
  git -C "$VESTS_DIR" sparse-checkout set testsuite/vests/vhdl-93
  git -C "$VESTS_DIR" checkout -q "$VESTS_COMMIT"
fi

html_escape()
{
  sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g'
}

# per-suite results, for the report
declare -a SUMMARY_ROWS
RESULT_ROWS=""
CRASHES=0

# Runs one suite; sets ACCEPTED, REJECTED, FAILED and TOTAL, and
# appends to RESULT_ROWS.
run_suite()
{
  local suite=$1
  local dir=$VESTS_DIR/testsuite/vests/vhdl-93/$suite
  ACCEPTED=0
  REJECTED=0
  FAILED=0
  TOTAL=0

  # the suites may have subdirectories
  for f in $(find "$dir" -name '*.vhd*' | sort); do
    TOTAL=$((TOTAL+1))
    local name
    name=${f#"$dir/"}
    local output status
    output=$(timeout 10 "$EBMC" "$f" --show-parse 2>&1) && status=0 || status=$?

    local class result
    if [ "$status" -eq 0 ]; then
      ACCEPTED=$((ACCEPTED+1)); class=ok; result=accepted
    elif [ "$status" -eq 1 ] && echo "$output" | grep -qE "^file .* line [0-9]+( column [0-9]+)?: "; then
      # a rejection by the parser, with a source location
      REJECTED=$((REJECTED+1)); class=rejected
      result=$(echo "$output" | grep -m1 -E "^file .* line [0-9]+( column [0-9]+)?: " | sed -E 's/^file [^:]*: //' | html_escape)
    else
      # a timeout (124), a signal (>= 128), or an internal error
      FAILED=$((FAILED+1)); class=fail
      if [ "$status" -eq 124 ]; then result="timeout";
      elif [ "$status" -ge 128 ]; then result="signal $((status-128))";
      else result="exit $status: $(echo "$output" | grep -m1 -iE "invariant|error" | html_escape)"; fi
      echo "FAILED: $suite/$name: $result"
    fi

    if [ -n "$REPORT" ]; then
      RESULT_ROWS+="<tr class=\"$class\"><td>$suite</td><td>$name</td><td>$result</td></tr>"$'\n'
    fi
  done

  CRASHES=$((CRASHES+FAILED))
}

status=0

while read -r suite baseline; do
  [ -z "$suite" ] && continue
  case "$suite" in \#*) continue;; esac

  run_suite "$suite"
  echo "$suite: $ACCEPTED of $TOTAL accepted by the parser, $REJECTED rejected, $FAILED crashed or timed out (baseline $baseline accepted)"
  SUMMARY_ROWS+=("<tr><td>$suite</td><td>$TOTAL</td><td>$ACCEPTED</td><td>$REJECTED</td><td>$FAILED</td><td>$baseline</td></tr>")

  # the baseline applies to the compliant suites only
  if [ "$baseline" != "-" ]; then
    if [ "$ACCEPTED" -lt "$baseline" ]; then
      echo "FAILED: fewer tests accepted than the baseline"
      status=1
    elif [ "$ACCEPTED" -gt "$baseline" ]; then
      echo "NOTE: more tests accepted than the baseline; raise it in baseline.txt"
    fi
  fi
done < "$BASELINE"

if [ "$CRASHES" -gt 0 ]; then
  echo "FAILED: $CRASHES crashes or timeouts"
  status=1
fi

if [ -n "$REPORT" ]; then
  VERSION=$("$EBMC" --version 2>/dev/null | head -1 | html_escape)
  VESTS_COMMIT=$(git -C "$VESTS_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)
  DATE=$(date -u +"%Y-%m-%d %H:%M UTC")

  cat > "$REPORT" <<EOF
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>EBMC VHDL parser acceptance: VESTs VHDL-93</title>
<style>
  :root { color-scheme: light dark; }
  body { font-family: -apple-system, system-ui, sans-serif; margin: 2rem auto;
         max-width: 60rem; padding: 0 1rem; line-height: 1.5; }
  h1 { margin-bottom: 0.25rem; }
  .meta { color: #666; font-size: 0.9rem; margin-bottom: 1.5rem; }
  table { border-collapse: collapse; width: 100%; margin-bottom: 2rem; }
  th, td { text-align: left; padding: 0.35rem 0.75rem; border-bottom: 1px solid #ddd; }
  th { position: sticky; top: 0; background: Canvas; }
  tr.ok td:last-child { color: #1a7f37; }
  tr.rejected td:last-child { color: #9a6700; }
  tr.fail td:last-child { color: #cf222e; }
</style>
</head>
<body>
<h1>VESTs VHDL-93: parser acceptance</h1>
<p class="meta">
  $VERSION &middot; VESTs at ghdl/ghdl@$VESTS_COMMIT &middot; $DATE
</p>
<p>
  The parser of the VHDL front-end is run over the tests of
  <a href="$VESTS_URL/tree/$VESTS_COMMIT/testsuite/vests/vhdl-93">VESTs</a>
  (Vhdl tESTs, University of Cincinnati / Clifton Labs) for
  IEEE 1076-1993. A test is accepted when <code>ebmc --show-parse</code>
  succeeds. This measures what the parser accepts, not compliance: type
  checking and synthesis are not exercised, the tests are simulation
  testbenches rather than RTL designs, and the non-compliant tests are
  mostly semantic errors, which a parser does not detect. Crashes and
  timeouts are reported separately.
</p>
<h2>Summary</h2>
<table>
<tr><th>Suite</th><th>Tests</th><th>Accepted</th><th>Rejected</th><th>Crashed or timed out</th><th>Baseline</th></tr>
$(printf '%s\n' "${SUMMARY_ROWS[@]}")
</table>
<h2>Results</h2>
<table>
<tr><th>Suite</th><th>Test</th><th>Result</th></tr>
$RESULT_ROWS
</table>
</body>
</html>
EOF
  echo "report written to $REPORT"
fi

exit $status
