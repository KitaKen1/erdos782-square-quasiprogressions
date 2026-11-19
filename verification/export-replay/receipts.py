"""Bind every kernel check and the FC statement comparison to one proof export."""

from pathlib import Path
from hashlib import sha256
import json
import subprocess
import sys


MAX_WORKERS = 12


def fail(message):
    raise SystemExit(message)


def file_digest(path):
    with path.open("rb") as stream:
        digest = sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
        return digest.hexdigest()


def chunk_path(directory, index):
    return directory / f"ExportReplayChunk{index}.olean"


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def checked_manifest(directory, expected_digest):
    manifest = directory / "manifest.json"
    if file_digest(manifest) != expected_digest:
        fail("Proof manifest does not match the preparation job.")
    result = json.loads(manifest.read_text())
    chunks = result["chunks"]
    for index, expected in enumerate(chunks):
        if file_digest(chunk_path(directory, index)) != expected:
            fail(f"Chunk {index} does not match the proof manifest.")
    indices = [i for group in result["groups"] for i in group]
    if sorted(indices) != list(range(len(chunks))):
        fail("The worker plan does not cover every chunk exactly once.")
    return result


def prepare(binary, proof, challenge, directory, batch_lines):
    proof_digest = file_digest(proof)
    challenge_digest = file_digest(challenge)
    subprocess.run([binary, "split", proof, directory, batch_lines], check=True)
    count = int((directory / "count").read_text())
    subprocess.run([binary, "compare", directory, str(count), challenge], check=True)
    if file_digest(proof) != proof_digest or file_digest(challenge) != challenge_digest:
        fail("The proof or challenge changed during preparation.")
    workers = min(MAX_WORKERS, count)
    groups = [[] for _ in range(workers)]
    sizes = [0 for _ in groups]
    chunk_sizes = [chunk_path(directory, i).stat().st_size for i in range(count)]
    for index in sorted(range(count), key=chunk_sizes.__getitem__, reverse=True):
        worker = min(range(workers), key=sizes.__getitem__)
        groups[worker].append(index)
        sizes[worker] += chunk_sizes[index]
    manifest = directory / "manifest.json"
    write_json(manifest, {
        "proof_sha256": proof_digest,
        "challenge_sha256": challenge_digest,
        "chunks": [file_digest(chunk_path(directory, i)) for i in range(count)],
        "groups": [sorted(group) for group in groups],
    })
    print(f"Prepared {count} chunks for {workers} workers")
    with Path(directory.parent / "actions-outputs.txt").open("w") as output:
        print(f"groups={json.dumps(list(range(workers)))}", file=output)
        print(f"manifest-sha256={file_digest(manifest)}", file=output)


def replay(binary, directory, manifest_digest, worker, receipt):
    manifest = checked_manifest(directory, manifest_digest)
    checked = []
    for index in manifest["groups"][worker]:
        subprocess.run([binary, "check", directory, str(index)], check=True)
        checked.append({"index": index, "sha256": manifest["chunks"][index]})
    write_json(receipt, {
        "worker": worker,
        "manifest_sha256": manifest_digest,
        "checked": checked,
    })


def finish(manifest_path, manifest_digest, receipts_dir, result):
    if file_digest(manifest_path) != manifest_digest:
        fail("Final manifest digest mismatch.")
    manifest = json.loads(manifest_path.read_text())
    chunks = manifest["chunks"]
    receipts = sorted(receipts_dir.glob("*/receipt.json"))
    seen_workers = set()
    seen_indices = set()
    for path in receipts:
        receipt = json.loads(path.read_text())
        worker = receipt["worker"]
        if (receipt["manifest_sha256"] != manifest_digest
                or not 0 <= worker < len(manifest["groups"])
                or worker in seen_workers):
            fail(f"Unexpected worker receipt: {path}")
        seen_workers.add(worker)
        expected = manifest["groups"][worker]
        if [item["index"] for item in receipt["checked"]] != expected:
            fail(f"Missing or unexpected chunks in worker {worker}")
        for item in receipt["checked"]:
            index = item["index"]
            if index in seen_indices or item["sha256"] != chunks[index]:
                fail(f"Unexpected proof chunk or digest: {index}")
            seen_indices.add(index)
    if seen_indices != set(range(len(chunks))) or seen_workers != set(range(len(manifest["groups"]))):
        fail("Missing verification receipts.")
    write_json(result, {
        "accepted": True,
        "kernel": "Lean",
        "chunks": len(chunks),
        "manifest_sha256": manifest_digest,
        "proof_sha256": manifest["proof_sha256"],
        "challenge_sha256": manifest["challenge_sha256"],
        "scope": "entire proof export of the exact pinned FC 782(i) negation",
    })
    print(f"Lean kernel accepted the entire proof export across {len(chunks)} chunks.")


def main():
    mode, *args = sys.argv[1:]
    if mode == "prepare":
        binary, proof, challenge, directory, batch_lines = args
        prepare(Path(binary), Path(proof), Path(challenge), Path(directory), batch_lines)
    elif mode == "replay":
        binary, directory, manifest, worker, receipt = args
        replay(Path(binary), Path(directory), manifest, int(worker), Path(receipt))
    elif mode == "finish":
        manifest, digest, receipts, result = args
        finish(Path(manifest), digest, Path(receipts), Path(result))
    else:
        fail("Expected prepare, replay, or finish.")


if __name__ == "__main__":
    main()
