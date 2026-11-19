"""Complete a replay from successful workers and individually checked chunks."""

import gzip
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


REPLAY_HOME = Path(__file__).resolve().parents[2] / "verification/export-replay"
sys.path.insert(0, str(REPLAY_HOME))
from receipts import checked_manifest, file_digest, finish, write_json


SLICES_PER_CHUNK = 5
SUBSLICES_PER_SLICE = 3


def successful_labels(jobs_path):
    jobs = json.loads(jobs_path.read_text())["jobs"]
    for job in jobs:
        match = re.fullmatch(r"replay-chunks \((\d+(?:-\d+)*)\)", job["name"])
        if match and job["conclusion"] == "success":
            yield match[1]


def successful_items(jobs_path, limit):
    result = []
    for label in successful_labels(jobs_path):
        index = int(label)
        if index in result or not 0 <= index < limit:
            raise SystemExit(f"Unexpected successful replay job {index}")
        result.append(index)
    return sorted(result)


def plan(manifest_path, jobs_path, chunk_jobs_path=None, slice_jobs_path=None,
         nested_jobs_path=None):
    manifest = json.loads(manifest_path.read_text())
    workers = successful_items(jobs_path, len(manifest["groups"]))
    covered = {index for worker in workers for index in manifest["groups"][worker]}
    count = len(manifest["chunks"])
    previous_chunks = (sorted(set(successful_items(chunk_jobs_path, count)) - covered)
                       if chunk_jobs_path else [])
    remaining = sorted(set(range(count)) - covered - set(previous_chunks))
    slices = SLICES_PER_CHUNK if chunk_jobs_path else 1
    slice_labels = [f"{index}-{part}" for index in remaining for part in range(slices)]
    previous_slices = (sorted(set(successful_labels(slice_jobs_path)).intersection(slice_labels))
                       if slice_jobs_path else [])
    subslices = SUBSLICES_PER_SLICE if slice_jobs_path else 0
    if subslices:
        items = [f"{label}-{part}" for label in slice_labels if label not in previous_slices
                 for part in range(subslices)]
    else:
        items = slice_labels if slices > 1 else remaining
    previous_nested = (sorted(set(successful_labels(nested_jobs_path)).intersection(items))
                       if nested_jobs_path else [])
    items = [item for item in items if item not in previous_nested]
    plan_data = {
        "workers": workers,
        "chunks": previous_chunks,
        "remaining": remaining,
        "slices": slices,
        "previous_slices": previous_slices,
        "subslice_count": subslices,
        "previous_nested": previous_nested,
    }
    print(f"replay-plan={json.dumps(plan_data)}")
    print(f"replay-items={json.dumps(items)}")
    print(f"previous-workers={json.dumps(workers)}")
    print(f"previous-chunks={json.dumps(previous_chunks)}")
    print(f"previous-slices={json.dumps(previous_slices)}")
    print(f"previous-nested={json.dumps(previous_nested)}")


def check(binary, directory, digest, item, receipt):
    manifest = checked_manifest(directory, digest)
    index_text, separator, label = item.partition("-")
    index = int(index_text)
    if not 0 <= index < len(manifest["chunks"]):
        raise SystemExit(f"Unexpected chunk {index}")
    info = {
        "index": index,
        "manifest_sha256": digest,
        "sha256": manifest["chunks"][index],
    }
    print(f"Replaying work item {item}.", flush=True)
    if separator:
        part, _, subpart = label.partition("-")
        options = [part, str(SLICES_PER_CHUNK)]
        if subpart:
            options.extend((subpart, str(SUBSLICES_PER_SLICE)))
        with tempfile.TemporaryDirectory(prefix="export-replay-prefix-") as scratch:
            hint = REPLAY_HOME / "projections" / digest / f"{item}.json.gz"
            command = "check-slice"
            if subpart and hint.is_file():
                hint_file = Path(scratch) / "visibility.json"
                hint_file.write_bytes(gzip.decompress(hint.read_bytes()))
                options.append(hint_file)
                command = "check-projection"
            output = subprocess.check_output(
                [binary, command, directory, scratch, str(index), *options], text=True)
        print(output, end="")
        match = re.fullmatch(
            r"Lean kernel accepted chunk (\d+), slice (\d+(?:-\d+)?) \((\d+) to (\d+) of (\d+) declarations\)\n",
            output)
        if not match or (int(match[1]), match[2]) != (index, label):
            raise SystemExit(f"Unexpected reply from the kernel checker for {item}")
        info["slice"] = int(part)
        if subpart:
            info["subslice"] = int(subpart)
        info["bounds"] = [int(match[3]), int(match[4])]
        info["total"] = int(match[5])
    else:
        subprocess.run([binary, "check", directory, str(index)], check=True)
    write_json(receipt, info)


def slice_receipts(directory, plan, index):
    for part in range(plan["slices"]):
        label = f"{index}-{part}"
        if label in plan.get("previous_slices", []):
            yield directory / "slices" / f"export-replay-chunk-{label}", {"slice": part}
        elif plan.get("subslice_count"):
            for subpart in range(plan["subslice_count"]):
                item = f"{label}-{subpart}"
                source = "nested" if item in plan.get("previous_nested", []) else "recovered"
                path = directory / source / f"export-replay-chunk-{item}"
                yield path, {"slice": part, "subslice": subpart}
        else:
            yield directory / "recovered" / f"export-replay-chunk-{label}", {"slice": part}


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
            for path, identity in slice_receipts(directory, plan, index):
                receipt = json.loads((path / "receipt.json").read_text())
                lo, hi = receipt["bounds"]
                if total is None:
                    total = receipt["total"]
                expected_slice = {**expected, **identity, "bounds": [lo, hi], "total": total}
                if receipt != expected_slice or lo != end or not lo < hi <= total:
                    raise SystemExit(f"Unexpected verification of {path.name}")
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
