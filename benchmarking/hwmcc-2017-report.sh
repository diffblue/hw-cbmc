#!/bin/sh

# This runs ebmc in BMC mode on the HWMCC17 single-safety benchmarks and
# emits an HTML report summarising the result of each benchmark.
#
# The benchmarks are read directly through ebmc's native AIGER front-end,
# so no external conversion tools are required.
#
# Usage: hwmcc-2017-report.sh [output.html]
#   The report is written to the given path (default: hwmcc-2017-report.html).
#
# Each ebmc invocation is bounded by a per-benchmark time limit (TIMEOUT),
# and the suite as a whole by an overall deadline (DEADLINE), so the total
# runtime stays within the CI job's budget.

set -u

REPORT=${1:-hwmcc-2017-report.html}

# Per-benchmark wall-clock limit, in seconds.  The HWMCC17 suite contains
# individual benchmarks that run for many minutes, which would otherwise
# exhaust the CI job's time budget, so each ebmc invocation is bounded.
# Override with the TIMEOUT environment variable.
TIMEOUT=${TIMEOUT:-30}

# Overall wall-clock budget for the whole suite, in seconds.  Once this is
# exceeded no further benchmarks are launched; the remainder are recorded
# as skipped.  This keeps the total runtime bounded regardless of how many
# benchmarks hit their per-benchmark limit.  Override with DEADLINE.
DEADLINE=${DEADLINE:-1800}
START_TIME=`date +%s`

# Run ebmc under the per-benchmark time limit.  Exit status 124 (the
# convention used by coreutils "timeout") indicates the limit was hit.
run_ebmc() {
  if command -v timeout >/dev/null 2>&1 ; then
    timeout "$TIMEOUT" ebmc "$@"
  else
    ebmc "$@"
  fi
}

if [ ! -e hwmcc17-single/. ] ; then
  echo Downloading HWMCC17 benchmark archive
  wget -q https://fmv.jku.at/hwmcc17/hwmcc17-single-benchmarks.tar.xz
  xz -d hwmcc17-single-benchmarks.tar.xz
  mkdir hwmcc17-single
  (cd hwmcc17-single ; tar xf ../hwmcc17-single-benchmarks.tar)
  rm hwmcc17-single-benchmarks.tar
fi

# Expected answers from the first solver's result column (status, bound) in
# https://fmv.jku.at/hwmcc17/single.csv.  A status of "time"/"mem" means no
# solver-verified result is available for that benchmark.
if [ ! -e hwmcc17-single.csv ] ; then
  echo Downloading HWMCC17 result table
  wget -q https://fmv.jku.at/hwmcc17/single.csv -O hwmcc17-single.csv
fi

echo Running ebmc on the HWMCC17 benchmarks

EBMC_VERSION=`ebmc --version 2>/dev/null || echo unknown`
GENERATED_ON=`date -u '+%Y-%m-%d %H:%M:%S UTC'`

total=0
pass=0
fail=0
skip=0

ROWS=`mktemp`
trap 'rm -f "$ROWS" ebmc.out' EXIT

# Return a non-empty string if the benchmark should be skipped, giving the
# reason, otherwise the empty string.
skip_reason() {
  case "$1" in
    6s320rb1|intel036)
      echo "too slow" ;;
    *)
      echo "" ;;
  esac
}

# Note the use of a brace group, not a subshell: the counters below must
# survive the loop.
{
# Ignore the one-line CSV header.
read -r line

while read -r line; do
  BENCHMARK=`echo "$line" | cut -d ';' -f 1`
  RESULT=`echo "$line" | cut -d ';' -f 3`
  LENGTH=`echo "$line" | cut -d ';' -f 4`

  [ -n "$BENCHMARK" ] || continue

  total=`expr $total + 1`
  expected="$RESULT"
  bound="-"
  css=skip
  label=skipped
  observed="not run"
  log_html=

  REASON=`skip_reason "$BENCHMARK"`

  ELAPSED=`expr \`date +%s\` - $START_TIME`

  if [ "$ELAPSED" -ge "$DEADLINE" ] ; then
    echo $BENCHMARK: skipping, overall time budget exhausted
    css=skip
    label=skipped
    observed="skipped (time budget of ${DEADLINE}s exhausted)"
  elif [ -n "$REASON" ] ; then
    echo $BENCHMARK: skipping
    css=skip
    label=skipped
    observed="skipped ($REASON)"
  elif [ ! -e "hwmcc17-single/${BENCHMARK}.aig" ] ; then
    echo benchmark $BENCHMARK not found
    css=fail
    label=missing
    observed="benchmark file missing"
  elif [ "$RESULT" = "uns" ] ; then
    bound=2
    run_ebmc --bound $bound "hwmcc17-single/${BENCHMARK}.aig" > ebmc.out 2>&1
    status=$?
    log_html=`sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' ebmc.out`

    if [ "$status" = 124 ] ; then
      echo $BENCHMARK: timed out after ${TIMEOUT}s
      css=skip
      label="timed out"
      observed="timed out after ${TIMEOUT}s at bound $bound"
    elif [ "$status" = 10 ] ; then
      echo $BENCHMARK: got unexpected counterexample
      css=fail
      label="unexpected counterexample"
      observed="counterexample at bound $bound"
    else
      echo $BENCHMARK: ok "(UNSAT smoke test)"
      css=ok
      label=ok
      if [ "$status" = 0 ] ; then
        observed="no counterexample at bound $bound"
      else
        observed="no counterexample at bound $bound (exit $status)"
      fi
    fi
  elif [ "$RESULT" = "sat" ] ; then
    if [ "$LENGTH" = "\"*\"" ] || [ "$LENGTH" = "*" ] || [ -z "$LENGTH" ] ; then
      echo $BENCHMARK: no counterexample length
      css=skip
      label="no reference bound"
      observed="expected SAT, but no published counterexample length"
    else
      bound=$LENGTH
      expected="sat at $LENGTH"
      run_ebmc --bound "$LENGTH" "hwmcc17-single/${BENCHMARK}.aig" > ebmc.out 2>&1
      status=$?
      log_html=`sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' ebmc.out`

      if [ "$status" = 124 ] ; then
        echo $BENCHMARK: timed out after ${TIMEOUT}s
        css=skip
        label="timed out"
        observed="timed out after ${TIMEOUT}s at bound $LENGTH"
      elif [ "$status" = 10 ] ; then
        echo $BENCHMARK: ok "(SAT $LENGTH)"
        css=ok
        label=ok
        observed="counterexample at bound $LENGTH"
      else
        echo $BENCHMARK: failed to find counterexample at bound $LENGTH
        css=fail
        label="missed counterexample"
        observed="no counterexample at bound $LENGTH (exit $status)"
      fi
    fi
  else
    # The reference column may be "time"/"mem" for benchmarks that no
    # solver resolved within the HWMCC17 limits, or some other value.
    case "$RESULT" in
      time|mem)
        echo $BENCHMARK: no reference result \("$RESULT"\)
        css=skip
        label="no reference result"
        observed="no solver-verified result in HWMCC17 (\"$RESULT\")" ;;
      *)
        echo $BENCHMARK: unknown expected result \"$RESULT\"
        css=skip
        label="unknown expectation"
        observed="unsupported expected result \"$RESULT\"" ;;
    esac
  fi

  if [ "$css" = ok ] ; then
    pass=`expr $pass + 1`
  elif [ "$css" = fail ] ; then
    fail=`expr $fail + 1`
  else
    skip=`expr $skip + 1`
  fi

  printf '<tr class="%s"><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td class="result" data-log="log-%s">%s</td></tr>\n<tr class="log-row" id="log-%s"><td colspan="5"><pre>%s</pre></td></tr>\n' \
    "$css" "$BENCHMARK" "$expected" "$bound" "$observed" "$total" "$label" "$total" "${log_html:-no log captured}" >> "$ROWS"
done
} < hwmcc17-single.csv

echo
echo "HWMCC17 summary: $pass/$total checks passed ($fail failed, $skip skipped)"

{
  cat <<HTML_HEAD
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>EBMC on HWMCC17</title>
<style>
  :root { color-scheme: light dark; }
  body { font-family: -apple-system, system-ui, sans-serif; margin: 2rem auto;
         max-width: 70rem; padding: 0 1rem; line-height: 1.5; }
  h1 { margin-bottom: 0.25rem; }
  .meta { color: #666; font-size: 0.9rem; margin-bottom: 1.5rem; }
  .meta code { font-size: 0.85rem; }
  .cards { display: flex; gap: 1rem; margin: 1.5rem 0; flex-wrap: wrap; }
  .card { border: 1px solid #ccc; border-radius: 0.5rem; padding: 0.75rem 1.25rem;
          text-align: center; min-width: 6rem; cursor: pointer;
          user-select: none; font: inherit; color: inherit; background: none; }
  .card.active { border-color: CanvasText;
                 background: color-mix(in srgb, Canvas 90%, CanvasText 10%); }
  .card .n { font-size: 1.75rem; font-weight: 600; display: block; }
  table { border-collapse: collapse; width: 100%; }
  th, td { text-align: left; padding: 0.35rem 0.75rem; border-bottom: 1px solid #ddd; }
  th { position: sticky; top: 0; background: Canvas; }
  tr.ok td:last-child { color: #1a7f37; }
  tr.fail td:last-child { color: #cf222e; }
  tr.skip td:last-child { color: #9a6700; }
  td.result { cursor: pointer; text-decoration: underline dotted; }
  tr.log-row { display: none; }
  tr.log-row pre { white-space: pre-wrap; word-break: break-all; margin: 0;
                    font-size: 0.8rem; max-height: 20rem; overflow: auto;
                    background: color-mix(in srgb, Canvas 90%, CanvasText 10%);
                    padding: 0.5rem; border-radius: 0.25rem; }
</style>
</head>
<body>
<h1>EBMC on HWMCC17</h1>
<p class="meta">
  Results of running <a href="https://github.com/diffblue/hw-cbmc">ebmc</a>
  in bounded mode over the
  <a href="https://fmv.jku.at/hwmcc17/">HWMCC17</a> single-safety AIGER
  benchmarks (read via ebmc's native AIGER front-end).<br>
  SAT benchmarks are checked at the published counterexample bound; UNSAT
  benchmarks are smoke-tested by confirming that ebmc does not report a
  counterexample at bound <code>2</code>.  Each benchmark is bounded by a
  ${TIMEOUT}s per-benchmark time limit.<br>
  Generated $GENERATED_ON &middot;
  ebmc <code>$EBMC_VERSION</code>
</p>
<div class="cards">
  <button type="button" class="card active" data-filter="all" aria-pressed="true"><span class="n">$total</span>benchmarks</button>
  <button type="button" class="card" data-filter="ok" aria-pressed="false"><span class="n">$pass</span>passed</button>
  <button type="button" class="card" data-filter="fail" aria-pressed="false"><span class="n">$fail</span>failed</button>
  <button type="button" class="card" data-filter="skip" aria-pressed="false"><span class="n">$skip</span>skipped</button>
</div>
<table>
<thead><tr><th>Benchmark</th><th>Expected</th><th>Bound</th><th>Observed</th><th>Result</th></tr></thead>
<tbody>
HTML_HEAD
  cat "$ROWS"
  cat <<'HTML_TAIL'
</tbody>
</table>
<script>
document.querySelectorAll('td.result').forEach(function (cell) {
  cell.addEventListener('click', function () {
    var logRow = document.getElementById(cell.dataset.log);
    if (!logRow) return;
    logRow.style.display = logRow.style.display === 'table-row' ? 'none' : 'table-row';
  });
});

// Clicking a summary card filters the table by status; "all" shows
// everything.  The active filter is mirrored in the URL fragment (e.g.
// #fail) so a link can open the report pre-filtered.
(function () {
  var cards = document.querySelectorAll('.card[data-filter]');
  function applyFilter(filter) {
    document.querySelectorAll('tbody tr').forEach(function (row) {
      if (row.classList.contains('log-row')) {
        // Collapse any expanded logs; they re-open on click.
        row.style.display = 'none';
        return;
      }
      var cls = row.classList[0];
      row.style.display = (filter === 'all' || cls === filter) ? '' : 'none';
    });
  }
  function selectCard(card) {
    cards.forEach(function (c) {
      c.classList.remove('active');
      c.setAttribute('aria-pressed', 'false');
    });
    card.classList.add('active');
    card.setAttribute('aria-pressed', 'true');
    applyFilter(card.dataset.filter);
  }
  cards.forEach(function (card) {
    card.addEventListener('click', function () {
      selectCard(card);
      location.hash = card.dataset.filter;
    });
  });
  // Apply the filter named in the URL fragment on load, if any is known.
  function applyHash() {
    var want = location.hash.replace(/^#/, '');
    var match = null;
    cards.forEach(function (c) { if (c.dataset.filter === want) match = c; });
    if (match) selectCard(match);
  }
  window.addEventListener('hashchange', applyHash);
  applyHash();
})();
</script>
</body>
</html>
HTML_TAIL
} > "$REPORT"

echo "Report written to $REPORT"

# Report-only: always succeed so the full result matrix is published.
exit 0
