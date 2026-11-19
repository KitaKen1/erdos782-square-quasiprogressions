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
PROFILED_PROOF = "891c600d9ffdef141ed03a3aca97ac6ad93cb9498b724376ad9e2f0397d36838"
PROFILED_MANIFEST = "ac298be825c50872f70f341ddc49831756830ae8a1eac99121e3fc05805bd9c9"


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
         nested_jobs_path=None, completed_jobs_path=None):
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
        "recovered_items": items,
    }
    print(f"replay-plan={json.dumps(plan_data)}")
    if completed_jobs_path:
        if not {str(item) for item in items} <= set(successful_labels(completed_jobs_path)):
            raise SystemExit("The completed replay run does not cover the remaining items.")
        print("replay-items=[]")
    else:
        print(f"replay-items={json.dumps(items)}")
    print(f"recovered-items={json.dumps(items)}")
    print(f"previous-workers={json.dumps(workers)}")
    print(f"previous-chunks={json.dumps(previous_chunks)}")
    print(f"previous-slices={json.dumps(previous_slices)}")
    print(f"previous-nested={json.dumps(previous_nested)}")


def fresh_plan(manifest_path, run_id):
    manifest = json.loads(manifest_path.read_text())
    indices = list(range(len(manifest["chunks"])))
    profiled = manifest["proof_sha256"] == PROFILED_PROOF and len(indices) == 33
    split_chunks = {7, 13, 25} if profiled else set()
    subdivided = ["7-4", "13-0", "25-1", "25-4"] if profiled else []
    whole = [i for i in indices if i not in split_chunks]
    items = [str(i) for i in whole]
    for i in sorted(split_chunks):
        for part in range(SLICES_PER_CHUNK):
            label = f"{i}-{part}"
            if label in subdivided:
                items.extend(f"{label}-{sub}" for sub in range(SUBSLICES_PER_SLICE))
            else:
                items.append(label)
    # These ranges and chunks took longest in the profiled export.
    priority = ["25-4-1", "25-1-0", "13-0-0", "7-4-2", "21", "24", "26", "19", "17"]
    if profiled:
        items = priority + [item for item in items if item not in priority]
    data = {
        "fresh_export_run": run_id,
        "workers": [],
        "chunks": [],
        "remaining": indices,
        "whole_chunks": whole,
        "slices": SLICES_PER_CHUNK,
        "subslice_count": SUBSLICES_PER_SLICE,
        "subdivided_slices": subdivided,
        "recovered_items": items,
    }
    print(f"fresh-export-plan={json.dumps(data)}")
    print(f"fresh-export-items={json.dumps(items)}")


def check(binary, directory, digest, item, receipt, fresh_run=""):
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
    if fresh_run:
        info["fresh_export_run"] = fresh_run
    print(f"Replaying work item {item}.", flush=True)
    if separator:
        part, _, subpart = label.partition("-")
        options = [part, str(SLICES_PER_CHUNK)]
        if subpart:
            options.extend((subpart, str(SUBSLICES_PER_SLICE)))
        with tempfile.TemporaryDirectory(prefix="export-replay-prefix-") as scratch:
            hint = REPLAY_HOME / "projections" / digest / f"{item}.json.gz"
            if (not hint.is_file() and manifest["proof_sha256"] == PROFILED_PROOF
                    and len(manifest["chunks"]) == 33):
                # These unfolding choices depend on the exported declarations,
                # whose byte sequence is fixed by proof_sha256.
                hint = REPLAY_HOME / "projections" / PROFILED_MANIFEST / f"{item}.json.gz"
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
        elif (plan.get("subslice_count")
              and label in plan.get("subdivided_slices", [label])):
            for subpart in range(plan["subslice_count"]):
                item = f"{label}-{subpart}"
                source = "nested" if item in plan.get("previous_nested", []) else "recovered"
                path = directory / source / f"export-replay-chunk-{item}"
                yield path, {"slice": part, "subslice": subpart}
        else:
            yield directory / "recovered" / f"export-replay-chunk-{label}", {"slice": part}


def normalize_receipt(directory, prefix, items):
    # download-artifact flattens a pattern that matches just one artifact.
    receipt = directory / "receipt.json"
    if not receipt.is_file():
        return
    if len(items) != 1:
        raise SystemExit(f"Unexpected flattened artifact in {directory}")
    destination = directory / f"{prefix}{items[0]}"
    destination.mkdir()
    receipt.rename(destination / receipt.name)
    log = directory / "replay.log"
    if log.is_file():
        log.rename(destination / log.name)


def combine(directory, digest, plan):
    manifest_path = directory / "manifest.json"
    if file_digest(manifest_path) != digest:
        raise SystemExit("Final manifest digest mismatch.")
    manifest = json.loads(manifest_path.read_text())
    for source, prefix, key in [
        ("previous", "export-replay-worker-", "workers"),
        ("continued", "export-replay-chunk-", "chunks"),
        ("slices", "export-replay-chunk-", "previous_slices"),
        ("nested", "export-replay-chunk-", "previous_nested"),
        ("recovered", "export-replay-chunk-", "recovered_items"),
    ]:
        normalize_receipt(directory / source, prefix, plan.get(key, []))
    workers = directory / "workers"
    covered = {}
    def chunk_info(index):
        info = {"index": index, "manifest_sha256": digest, "sha256": manifest["chunks"][index]}
        if "fresh_export_run" in plan:
            info["fresh_export_run"] = plan["fresh_export_run"]
        return info

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
        if plan["slices"] == 1 or index in plan.get("whole_chunks", []):
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
    elif command == "fresh-plan":
        manifest, run_id = args
        fresh_plan(Path(manifest), run_id)
    elif command == "check":
        binary, directory, digest, index, receipt, *fresh_run = args
        check(Path(binary), Path(directory), digest, index, Path(receipt), *fresh_run)
    elif command == "combine":
        directory, digest, plan_json = args
        combine(Path(directory), digest, json.loads(plan_json))
    else:
        raise SystemExit("Expected plan, fresh-plan, check, or combine.")
