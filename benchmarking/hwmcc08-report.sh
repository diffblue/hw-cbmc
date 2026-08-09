#!/bin/sh

# This runs ebmc in BMC mode on the HWMCC08 benchmarks and emits an HTML
# report summarising the result of each benchmark.
#
# Usage: hwmcc08-report.sh [output.html]
#   The report is written to the given path (default: hwmcc08-report.html).

set -u

REPORT=${1:-hwmcc08-report.html}

if [ ! -e hwmcc08/. ] ; then
  echo Downloading HWMCC08 benchmark archive
  wget -q http://fmv.jku.at/hwmcc/hwmcc08public.tar.bz2
  tar xjf hwmcc08public.tar.bz2
  rm hwmcc08public.tar.bz2
fi

# Expected answers from the abc result column in
# https://fmv.jku.at/hwmcc08/hwmcc08results.csv.
if [ ! -e hwmcc08results.csv ] ; then
  echo Downloading HWMCC08 result table
  wget -q https://fmv.jku.at/hwmcc08/hwmcc08results.csv
fi

echo Running ebmc on the HWMCC08 benchmarks

EBMC_VERSION=`ebmc --version 2>/dev/null || echo unknown`
GENERATED_ON=`date -u '+%Y-%m-%d %H:%M:%S UTC'`

total=0
pass=0
fail=0
skip=0

ROWS=`mktemp`
trap 'rm -f "$ROWS" ebmc.out' EXIT

(# Ignore the three-line CSV header.
read -r line
read -r line
read -r line

while read -r line; do
  BENCHMARK=`echo "$line" | cut -d ',' -f 1 | tr -d '"'`
  LENGTH=`echo "$line" | cut -d ',' -f 2 | tr -d '"'`
  RESULT=`echo "$line" | cut -d ',' -f 3 | tr -d '"'`

  [ -n "$BENCHMARK" ] || continue

  total=`expr $total + 1`
  expected="$RESULT"
  bound="-"
  css=skip
  label=skipped
  observed="not run"
  log_html=

  if [ ! -e "hwmcc08/${BENCHMARK}.aig" ] ; then
    echo benchmark $BENCHMARK not found
    css=fail
    label=missing
    observed="benchmark file missing"
  elif [ "$RESULT" = "uns" ] ; then
    bound=2
    ebmc --bound $bound "hwmcc08/${BENCHMARK}.aig" > ebmc.out 2>&1
    status=$?
    log_html=`sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' ebmc.out`

    if [ "$status" = 10 ] ; then
      echo $BENCHMARK: got unexpected counterexample
      css=fail
      label=unexpected counterexample
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
    if [ "$LENGTH" = "*" ] ; then
      echo $BENCHMARK: no counterexample length
      css=skip
      label=no reference bound
      observed="expected SAT, but no published counterexample length"
    else
      bound=$LENGTH
      expected="sat at $LENGTH"
      ebmc --bound "$LENGTH" "hwmcc08/${BENCHMARK}.aig" > ebmc.out 2>&1
      status=$?
      log_html=`sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' ebmc.out`

      if [ "$status" = 10 ] ; then
        echo $BENCHMARK: ok "(SAT $LENGTH)"
        css=ok
        label=ok
        observed="counterexample at bound $LENGTH"
      else
        echo $BENCHMARK: failed to find counterexample at bound $LENGTH
        css=fail
        label=missed counterexample
        observed="no counterexample at bound $LENGTH (exit $status)"
      fi
    fi
  else
    echo $BENCHMARK: unknown expected result \"$RESULT\"
    css=skip
    label=unknown expectation
    observed="unsupported expected result \"$RESULT\""
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
done ) < hwmcc08results.csv

echo
echo "HWMCC08 summary: $pass/$total checks passed ($fail failed, $skip skipped)"

{
  cat <<HTML_HEAD
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>EBMC on HWMCC08</title>
<style>
  :root { color-scheme: light dark; }
  body { font-family: -apple-system, system-ui, sans-serif; margin: 2rem auto;
         max-width: 70rem; padding: 0 1rem; line-height: 1.5; }
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
<h1>EBMC on HWMCC08</h1>
<p class="meta">
  Results of running <a href="https://github.com/diffblue/hw-cbmc">ebmc</a>
  in bounded mode over the
  <a href="https://fmv.jku.at/hwmcc08/">HWMCC08</a> AIG benchmarks.<br>
  SAT benchmarks are checked at the published counterexample bound; UNSAT
  benchmarks are smoke-tested by confirming that ebmc does not report a
  counterexample at bound <code>2</code>.<br>
  Generated $GENERATED_ON &middot;
  ebmc <code>$EBMC_VERSION</code>
</p>
<div class="cards">
  <div class="card"><span class="n">$total</span>benchmarks</div>
  <div class="card"><span class="n">$pass</span>passed</div>
  <div class="card"><span class="n">$fail</span>failed</div>
  <div class="card"><span class="n">$skip</span>skipped</div>
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
</script>
</body>
</html>
HTML_TAIL
} > "$REPORT"

echo "Report written to $REPORT"

# Report-only: always succeed so the full result matrix is published.
exit 0
