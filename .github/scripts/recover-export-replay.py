"""Complete a replay from successful workers and individually checked chunks."""

import json
from pathlib import Path
import re
import subprocess
import sys


sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "verification/export-replay"))
from receipts import checked_manifest, file_digest, finish, write_json


def plan(manifest_path, jobs_path):
    manifest = json.loads(manifest_path.read_text())
    jobs = json.loads(jobs_path.read_text())["jobs"]
    workers = []
    for job in jobs:
        match = re.fullmatch(r"replay-chunks \((\d+)\)", job["name"])
        if match and job["conclusion"] == "success":
            index = int(match[1])
            if index in workers or not 0 <= index < len(manifest["groups"]):
                raise SystemExit(f"Unexpected successful replay worker {index}")
            workers.append(index)
    covered = {index for worker in workers for index in manifest["groups"][worker]}
    remaining = sorted(set(range(len(manifest["chunks"]))) - covered)
    print(f"previous-workers={json.dumps(sorted(workers))}")
    print(f"remaining-chunks={json.dumps(remaining)}")


def check(binary, directory, digest, index, receipt):
    manifest = checked_manifest(directory, digest)
    if not 0 <= index < len(manifest["chunks"]):
        raise SystemExit(f"Unexpected chunk {index}")
    print(f"Replaying chunk {index}.", flush=True)
    subprocess.run([binary, "check", directory, str(index)], check=True)
    write_json(receipt, {
        "index": index,
        "manifest_sha256": digest,
        "sha256": manifest["chunks"][index],
    })


def combine(directory, digest, previous_workers, remaining):
    manifest_path = directory / "manifest.json"
    if file_digest(manifest_path) != digest:
        raise SystemExit("Final manifest digest mismatch.")
    manifest = json.loads(manifest_path.read_text())
    workers = directory / "workers"
    covered = {}
    for worker in previous_workers:
        receipt_path = directory / "previous" / f"export-replay-worker-{worker}" / "receipt.json"
        receipt = json.loads(receipt_path.read_text())
        expected = {
            "worker": worker,
            "manifest_sha256": digest,
            "checked": [
                {"index": index, "sha256": manifest["chunks"][index]}
                for index in manifest["groups"][worker]
            ],
        }
        if receipt != expected:
            raise SystemExit(f"Previous worker {worker} did not check the expected chunks.")
        for item in receipt["checked"]:
            if item["index"] in covered:
                raise SystemExit(f"Duplicate chunk {item['index']}")
            covered[item["index"]] = item
    for index in remaining:
        receipt_path = directory / "recovered" / f"export-replay-chunk-{index}" / "receipt.json"
        receipt = json.loads(receipt_path.read_text())
        expected = {"index": index, "manifest_sha256": digest, "sha256": manifest["chunks"][index]}
        if receipt != expected or index in covered:
            raise SystemExit(f"Unexpected receipt for recovered chunk {index}")
        covered[index] = {"index": index, "sha256": receipt["sha256"]}
    if set(covered) != set(range(len(manifest["chunks"]))):
        raise SystemExit("Missing verification receipts.")
    for worker, group in enumerate(manifest["groups"]):
        path = workers / f"export-replay-worker-{worker}" / "receipt.json"
        path.parent.mkdir(parents=True)
        write_json(path, {
            "worker": worker,
            "manifest_sha256": digest,
            "checked": [covered[index] for index in group],
        })
    finish(manifest_path, digest, workers, directory / "result.json")


if __name__ == "__main__":
    command, *args = sys.argv[1:]
    if command == "plan":
        plan(*map(Path, args))
    elif command == "check":
        binary, directory, digest, index, receipt = args
        check(Path(binary), Path(directory), digest, int(index), Path(receipt))
    elif command == "combine":
        directory, digest, previous, remaining = args
        combine(Path(directory), digest, json.loads(previous), json.loads(remaining))
    else:
        raise SystemExit("Expected plan, check, or combine.")
