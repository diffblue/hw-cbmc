#!/bin/bash
# Run gt_flow.sh over a manifest inside the openroad/orfs container.
# Usage: [PLATFORM=<name>] run_gt.sh <manifest.tsv> <workdir> <out.tsv> [jobs]
# Paths in the manifest must be under the mounted directories (the
# manifest's directory tree and this repository are mounted at the same
# paths inside the container).

set -eu
manifest=$(realpath "$1"); work=$(realpath -m "$2"); out=$(realpath -m "$3")
jobs=${4:-8}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
mkdir -p "$work"

mounts="-v $repo:$repo"
for d in $(cut -f4 "$manifest" | tr ' ' '\n' | grep . | xargs -n1 dirname \
           | sort -u | awk -F/ '{print "/"$2"/"$3}' | sort -u); do
  case "$d" in "$repo"*) ;; *) mounts="$mounts -v $d:$d" ;; esac
done

# Each container process gets a 4 GiB address-space cap.
docker run --rm --memory=48g --user "$(id -u):$(id -g)" -e HOME=/tmp -e PLATFORM="${PLATFORM:-nangate45}" $mounts -v "$work:$work" openroad/orfs:latest \
  bash -c "
    awk -F'\t' '\$3!=\"\" && \$7==\"\"' '$manifest' \
    | tr '\t' '\034' \
    | xargs -P $jobs -d '\n' -I{} bash -c '
        IFS=\$'\''\034'\'' read -r set name top src inc def err <<< \"{}\"
        ulimit -v 4194304
        $here/gt_flow.sh $work \"\$name\" \"\$top\" \"\$src\" \"\$inc\" \"\$def\"
      '
  " > "$out.tmp"
sort "$out.tmp" > "$out" && rm -f "$out.tmp"
awk -F'\t' '{print $2}' "$out" | sort | uniq -c
