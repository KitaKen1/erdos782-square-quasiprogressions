#!/usr/bin/env bash
# Restore the checksum-pinned public Linux build cache into the Lake workspace.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cache_dir="$(mktemp -d)"
trap 'rm -rf "$cache_dir"' EXIT
python3 - "$root" "$cache_dir" <<'PY'
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root, cache_dir = map(Path, sys.argv[1:])
spec = json.loads((root / "verification/axiom-cache.json").read_text())
manifest = json.loads((root / "lean/lake-manifest.json").read_text())
versions = {p["name"]: p["rev"] for p in manifest["packages"]}
for package in ("mathlib", "Stacks", "Mordell"):
    if versions[package] != spec["cache_manifest"][package]:
        raise SystemExit(f"Cache revision differs from Lake's pin for {package}.")
toolchain = (root / "lean/lean-toolchain").read_text().strip()
if toolchain != "leanprover/lean4:" + spec["cache_manifest"]["lean"]:
    raise SystemExit("Cache toolchain differs from the project's pin.")

whole = hashlib.sha256()
for part in spec["parts"]:
    path = cache_dir / part["name"]
    url = f'https://github.com/{spec["repository"]}/releases/download/{spec["release_tag"]}/{path.name}'
    subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                    "--retry", "3", "--proto", "=https", url, "--output", str(path)], check=True)
    with path.open("rb") as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            digest.update(block)
            whole.update(block)
    if path.stat().st_size != part["bytes"] or digest.hexdigest() != part["sha256"]:
        raise SystemExit(f"Cache part differs from the pinned release: {path.name}")
if whole.hexdigest() != spec["archive_sha256"]:
    raise SystemExit("The concatenated cache differs from the pinned release.")
print("Verified the public Stacks and Mordell cache.")
PY
cat "$cache_dir"/*.part-* | zstd -dc | tar -x --no-same-owner --no-same-permissions \
  -C "$root/lean/.lake/packages" Stacks/.lake/build Mordell/.lake/build
