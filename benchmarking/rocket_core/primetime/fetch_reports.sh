#!/bin/sh
# Download the PrimeTime reports from the pinned RTL-Timer commit into this
# directory, verify them against SHA256SUMS, and generate
# Rocket.hier_cell_area.txt (the per-module area extract) from the full
# per-cell report. See NOTICE for the license.
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
  if [ ! -f "downloads/$f" ]; then
    echo "fetching $f"
    curl -sfL "$BASE/$f" -o "downloads/$f"
  fi
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

# Install the reports next to this script.
cp downloads/Rocket.qor.rpt downloads/Rocket.total_area.rpt \
   downloads/Rocket.report_power.rpt downloads/Rocket.report_power_hier.rpt \
   downloads/Rocket.hier_cell_area.txt .
