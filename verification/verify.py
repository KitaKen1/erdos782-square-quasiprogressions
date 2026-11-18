"""Compare the conditional answer to Erdős 782(i) against its challenge."""

from argparse import ArgumentParser
import json
from pathlib import Path
import subprocess


VERIFICATION = Path(__file__).resolve().parent
LEAN = VERIFICATION.parent / "lean"
RESULTS = VERIFICATION / "results"
VERDICTS = (
    "nanoda kernel accepts the solution",
    "Lean default kernel accepts the solution",
    "Your solution is okay!",
)


def run(log_name, command):
    result = subprocess.run(
        command, cwd=LEAN, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        encoding="utf-8", check=False,
    )
    (RESULTS / log_name).write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    return result.stdout


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--trusted-local", action="store_true",
        help="Run this trusted checkout without Lake's Linux bubblewrap sandbox",
    )
    args = parser.parse_args()

    RESULTS.mkdir(exist_ok=True)
    for receipt in ("result.json", "replay-status.txt"):
        (RESULTS / receipt).unlink(missing_ok=True)
    run("build.log", ["lake", "--wfail", "build", "Comparator.Challenge", "Comparator.Candidate"])
    run("statement.log", ["lake", "env", "lean", "../verification/Check.lean"])

    command = ["lake", "env", "lake", "comparator"]
    if args.trusted_local:
        command.append("--inadvisably-no-sandbox")
    log = run("fc-target.log", command)
    if any(verdict not in log for verdict in VERDICTS):
        raise SystemExit("Comparator did not report acceptance by both kernels.")

    config = json.loads((LEAN / "comparator.json").read_text(encoding="utf-8"))
    receipt = {
        "accepted": True,
        "targets": config["theorem_names"],
        "kernels": ["Lean", "nanoda"],
        "lake_bubblewrap": not args.trusted_local,
        "scope": "conditional reduction for Erdős 782(i)",
    }
    (RESULTS / "result.json").write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8",
    )


if __name__ == "__main__":
    main()
