#!/bin/sh
# Re-download the PrimeTime reports from the pinned RTL-Timer commit and
# verify that the copies checked into this directory match upstream
# byte-for-byte. Also regenerates Rocket.hier_cell_area.txt (the
# per-module area extract) from the full per-cell report, which is too
# large (1 MB) to check in.
#
# Usage: ./fetch_reports.sh
# Requires: curl, shasum (or sha256sum).

set -eu
cd "$(dirname "$0")"

COMMIT=206ff4078368c251d2fafaffcc648282c68316f1
BASE="https://raw.githubusercontent.com/hkust-zhiyao/RTL-Timer/$COMMIT/report_example/rpt_data/net/Rocket_TinyRocket_route_TYP_SAIF_SDF"

FILES="Rocket.qor.rpt Rocket.total_area.rpt Rocket.report_power.rpt Rocket.report_power_hier.rpt Rocket.cell_pwr_area.rpt"

mkdir -p downloads

for f in $FILES; do
  echo "fetching $f"
  curl -sfL "$BASE/$f" -o "downloads/$f"
done

# Regenerate the per-module area extract: the rows of the per-cell
# power/area report flagged 'h' (hierarchical cell), whose Area column
# is the module instance's total cell area.
{
  echo "# Extracted from Rocket.cell_pwr_area.rpt (see SHA256SUMS),"
  echo "# RTL-Timer commit $COMMIT,"
  echo "# by fetch_reports.sh: the rows with attribute 'h'"
  echo "# (hierarchical cell). Columns: cell, internal/switching/"
  echo "# leakage/total power (W), (% of total), area (um2), attrs."
  grep -E ' h[[:space:]]*$' downloads/Rocket.cell_pwr_area.rpt
} > downloads/Rocket.hier_cell_area.txt

# Verify downloads and the regenerated extract against the recorded
# checksums.
if command -v shasum >/dev/null 2>&1; then
  SHA="shasum -a 256"
else
  SHA="sha256sum"
fi
(cd downloads && $SHA -c ../SHA256SUMS)

# Compare everything against the checked-in copies.
status=0
for f in Rocket.qor.rpt Rocket.total_area.rpt Rocket.report_power.rpt \
         Rocket.report_power_hier.rpt Rocket.hier_cell_area.txt; do
  if cmp -s "downloads/$f" "$f"; then
    echo "OK: $f matches upstream"
  else
    echo "MISMATCH: $f differs from upstream" >&2
    status=1
  fi
done
exit $status
