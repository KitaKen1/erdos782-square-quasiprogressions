#!/usr/bin/env bash
# Restore dependency archives produced by earlier jobs in this workflow run.
set -euo pipefail
packages="$(cd "$(dirname "$0")/../lean/.lake/packages" && pwd)"
while IFS= read -r -d '' archive; do
  filename="$(basename "$archive")"
  level="${filename#wave-}"
  level="${level%%-*}"
  if [[ "$level" =~ ^[0-9]+$ ]] && (( level < $1 )); then
    tar --zstd -xf "$archive" --no-same-owner --no-same-permissions -C "$packages"
    rm -- "$archive"
  fi
done < <(find "$2" -type f -name 'wave-*-shard-*.tar.zst' -print0)
