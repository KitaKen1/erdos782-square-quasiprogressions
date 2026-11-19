"""Preserve the verification artifacts from a successful GitHub Actions attempt."""

from argparse import ArgumentParser
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import subprocess
from zipfile import ZipFile


def github(repo, path):
    return subprocess.check_output(["gh", "api", "--method", "GET", f"repos/{repo}/{path}"])


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--run", type=int, required=True)
    parser.add_argument("--attempt", type=int, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("Choose a new output directory.")

    run = f"actions/runs/{args.run}"
    attempt_path = f"{run}/attempts/{args.attempt}"
    attempt_data = github(args.repo, attempt_path)
    attempt = json.loads(attempt_data)
    if (attempt["conclusion"], attempt["run_attempt"], attempt["head_sha"]) != (
        "success", args.attempt, args.expected_commit,
    ):
        raise SystemExit("Expected a successful attempt on the specified commit.")

    artifacts_data = github(args.repo, f"{run}/artifacts?per_page=100")
    listing = json.loads(artifacts_data)
    name = f"comparator-{args.run}-{args.attempt}"
    matches = [artifact for artifact in listing["artifacts"] if artifact["name"] == name]
    if listing["total_count"] > 100 or len(matches) != 1 or matches[0]["expired"]:
        raise SystemExit(f"Expected one available artifact named {name}.")
    artifact = matches[0]
    proof_zip = github(args.repo, f'actions/artifacts/{artifact["id"]}/zip')
    if artifact.get("digest") != f"sha256:{sha256(proof_zip).hexdigest()}":
        raise SystemExit("The artifact does not match its GitHub SHA-256 digest.")

    with ZipFile(BytesIO(proof_zip)) as archive:
        if archive.testzip() is not None:
            raise SystemExit("The artifact ZIP failed its integrity check.")
        files = {
            name: archive.read(name)
            for name in ("result.json", "fc-target.log", "replay-status.txt")
        }
        for name in ("statement.log", "replay.log"):
            if name in archive.namelist():
                files[name] = archive.read(name)
    result = json.loads(files["result.json"])
    kernels = result.get("kernels")
    log = files["fc-target.log"]
    if (result.get("accepted") is not True or result.get("lake_bubblewrap") is not True
            or result.get("targets") not in (
                ["Erdos782.erdos_782.parts.i_neg"], ["Erdos782.part_i_negative"],
            )
            or files["replay-status.txt"] != b"PASS\n"
            or kernels not in (["Lean"], ["Lean", "nanoda"])
            or b"Lean default kernel accepts the solution" not in log
            or b"Your solution is okay!" not in log
            or (kernels == ["Lean", "nanoda"] and (
                b"nanoda kernel accepts the solution" not in log or "replay.log" not in files
            ))):
        raise SystemExit("Expected a passing sandboxed Comparator check and fresh replay.")

    workflow_zip = github(args.repo, f"{attempt_path}/logs")
    with ZipFile(BytesIO(workflow_zip)) as archive:
        if archive.testzip() is not None:
            raise SystemExit("The workflow logs ZIP failed its integrity check.")
    files.update({
        "attempt.json": attempt_data,
        "artifacts.json": artifacts_data,
        "comparator.zip": proof_zip,
        "workflow-logs.zip": workflow_zip,
    })
    args.output.mkdir(parents=True)
    for filename, data in files.items():
        (args.output / filename).write_bytes(data)
    checksums = "".join(
        f"{sha256(data).hexdigest()}  {name}\n" for name, data in sorted(files.items())
    )
    (args.output / "SHA256SUMS").write_text(checksums, encoding="utf-8")
    print(f'Archived {attempt["html_url"]} to {args.output}')


if __name__ == "__main__":
    main()
