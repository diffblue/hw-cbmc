#!/bin/sh
# Download the Rocket core RTL from the pinned RTL-Timer commit and extract
# the Rocket module and the modules it instantiates into rocket_full.v.
#
# rocket_full.v is plusarg_reader.v followed by the modules RVCExpander
# through Rocket (contiguous in the upstream file) of
# chipyard.TestHarness.TinyRocketConfig.top.v. RTL-Timer is distributed
# under the BSD 3-Clause License, Copyright (c) 2024, Wenji Fang; the
# modules originate from rocket-chip and chipyard.
#
# Usage: ./fetch_rtl.sh
# Requires: curl, awk, sed, sha256sum (or shasum).

set -eu
cd "$(dirname "$0")"

COMMIT=206ff4078368c251d2fafaffcc648282c68316f1
BASE="https://raw.githubusercontent.com/hkust-zhiyao/RTL-Timer/$COMMIT/vlg2bog/rtl_example/chipyard/rtl/TinyRocket"

if command -v sha256sum >/dev/null 2>&1; then
  SHA="sha256sum"
else
  SHA="shasum -a 256"
fi

mkdir -p downloads
for f in chipyard.TestHarness.TinyRocketConfig.top.v plusarg_reader.v; do
  if [ ! -f "downloads/$f" ]; then
    echo "fetching $f"
    curl -sfL "$BASE/$f" -o "downloads/$f"
  fi
done

top=downloads/chipyard.TestHarness.TinyRocketConfig.top.v
first=$(grep -n '^module RVCExpander(' "$top" | cut -d: -f1)
rocket=$(grep -n '^module Rocket(' "$top" | cut -d: -f1)
last=$(awk -v s="$rocket" 'NR > s && /^endmodule/ { print NR; exit }' "$top")

{
  cat downloads/plusarg_reader.v
  sed -n "${first},${last}p" "$top"
} > rocket_full.v

$SHA -c SHA256SUMS
