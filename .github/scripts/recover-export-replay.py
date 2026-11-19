"""Complete a replay from successful workers and individually checked chunks."""

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "verification/export-replay"))
from receipts import checked_manifest, file_digest, finish, write_json


SLICES_PER_CHUNK = 5


def successful_items(jobs_path, limit):
    jobs = json.loads(jobs_path.read_text())["jobs"]
    result = []
    for job in jobs:
        match = re.fullmatch(r"replay-chunks \((\d+)\)", job["name"])
        if match and job["conclusion"] == "success":
            index = int(match[1])
            if index in result or not 0 <= index < limit:
                raise SystemExit(f"Unexpected successful replay job {index}")
            result.append(index)
    return sorted(result)


def plan(manifest_path, jobs_path, chunk_jobs_path=None):
    manifest = json.loads(manifest_path.read_text())
    workers = successful_items(jobs_path, len(manifest["groups"]))
    covered = {index for worker in workers for index in manifest["groups"][worker]}
    count = len(manifest["chunks"])
    previous_chunks = (sorted(set(successful_items(chunk_jobs_path, count)) - covered)
                       if chunk_jobs_path else [])
    remaining = sorted(set(range(count)) - covered - set(previous_chunks))
    slices = SLICES_PER_CHUNK if chunk_jobs_path else 1
    items = ([f"{index}-{part}" for index in remaining for part in range(slices)]
             if slices > 1 else remaining)
    print(f"replay-plan={json.dumps({'workers': workers, 'chunks': previous_chunks, 'remaining': remaining, 'slices': slices})}")
    print(f"replay-items={json.dumps(items)}")
    print(f"previous-workers={json.dumps(workers)}")
    print(f"previous-chunks={json.dumps(previous_chunks)}")


def check(binary, directory, digest, item, receipt):
    manifest = checked_manifest(directory, digest)
    index, separator, part = item.partition("-")
    index = int(index)
    if not 0 <= index < len(manifest["chunks"]):
        raise SystemExit(f"Unexpected chunk {index}")
    info = {
        "index": index,
        "manifest_sha256": digest,
        "sha256": manifest["chunks"][index],
    }
    print(f"Replaying work item {item}.", flush=True)
    if separator:
        with tempfile.TemporaryDirectory(prefix="export-replay-prefix-") as scratch:
            output = subprocess.check_output(
                [binary, "check-slice", directory, scratch, str(index), part,
                 str(SLICES_PER_CHUNK)], text=True)
        print(output, end="")
        match = re.fullmatch(
            r"Lean kernel accepted chunk (\d+), slice (\d+) \((\d+) to (\d+) of (\d+) declarations\)\n",
            output)
        if not match or (int(match[1]), int(match[2])) != (index, int(part)):
            raise SystemExit(f"Unexpected reply from the kernel checker for {item}")
        info["slice"] = int(part)
        info["bounds"] = [int(match[3]), int(match[4])]
        info["total"] = int(match[5])
    else:
        subprocess.run([binary, "check", directory, str(index)], check=True)
    write_json(receipt, info)


def combine(directory, digest, plan):
    manifest_path = directory / "manifest.json"
    if file_digest(manifest_path) != digest:
        raise SystemExit("Final manifest digest mismatch.")
    manifest = json.loads(manifest_path.read_text())
    workers = directory / "workers"
    covered = {}
    def chunk_info(index):
        return {"index": index, "manifest_sha256": digest, "sha256": manifest["chunks"][index]}

    for worker in plan["workers"]:
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
    for index in plan["chunks"]:
        receipt_path = directory / "continued" / f"export-replay-chunk-{index}" / "receipt.json"
        receipt = json.loads(receipt_path.read_text())
        if receipt != chunk_info(index) or index in covered:
            raise SystemExit(f"Unexpected receipt for previously replayed chunk {index}")
        covered[index] = {"index": index, "sha256": receipt["sha256"]}
    for index in plan["remaining"]:
        expected = chunk_info(index)
        if index in covered:
            raise SystemExit(f"Duplicate chunk {index}")
        if plan["slices"] == 1:
            receipt_path = directory / "recovered" / f"export-replay-chunk-{index}" / "receipt.json"
            receipt = json.loads(receipt_path.read_text())
            valid = receipt == expected
        else:
            end = 0
            total = None
            for part in range(plan["slices"]):
                receipt_path = directory / "recovered" / f"export-replay-chunk-{index}-{part}" / "receipt.json"
                receipt = json.loads(receipt_path.read_text())
                lo, hi = receipt["bounds"]
                if total is None:
                    total = receipt["total"]
                expected_slice = {**expected, "slice": part, "bounds": [lo, hi], "total": total}
                if receipt != expected_slice or lo != end or not lo < hi <= total:
                    raise SystemExit(f"Unexpected verification of chunk {index} slice {part}")
                end = hi
            valid = end == total
        if not valid:
            raise SystemExit(f"Unexpected receipt for recovered chunk {index}")
        covered[index] = {"index": index, "sha256": expected["sha256"]}
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
    write_json(directory / "replay-plan.json", plan)
    finish(manifest_path, digest, workers, directory / "result.json")


if __name__ == "__main__":
    command, *args = sys.argv[1:]
    if command == "plan":
        plan(*map(Path, args))
    elif command == "check":
        binary, directory, digest, index, receipt = args
        check(Path(binary), Path(directory), digest, index, Path(receipt))
    elif command == "combine":
        directory, digest, plan_json = args
        combine(Path(directory), digest, json.loads(plan_json))
    else:
        raise SystemExit("Expected plan, check, or combine.")
