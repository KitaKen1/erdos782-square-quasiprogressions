"""Compare the unconditional answer to Erdős 782(i) against its challenge."""

from argparse import ArgumentParser
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


VERIFICATION = Path(__file__).resolve().parent
LEAN = VERIFICATION.parent / "lean"
RESULTS = VERIFICATION / "results"
VERDICTS = (
    "nanoda kernel accepts the solution",
    "Lean default kernel accepts the solution",
    "Your solution is okay!",
)


def run(log_name, command, cwd=LEAN):
    result = subprocess.run(
        command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        encoding="utf-8", check=False,
    )
    (RESULTS / log_name).write_text(result.stdout, encoding="utf-8")
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    return result.stdout


def prepare_challenge(directory):
    """Build the reference using only the same pinned Mathlib dependency."""
    (directory / "Comparator").mkdir()
    for name in ("FCStatement.lean", "Challenge.lean"):
        source = LEAN / "Comparator" / name
        (directory / "Comparator" / name).write_bytes(source.read_bytes())
    for name in ("lean-toolchain", "comparator.json"):
        (directory / name).write_bytes((LEAN / name).read_bytes())
    manifest = json.loads((LEAN / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["packages"] = [
        package for package in manifest["packages"] if package["name"] not in {"Mordell", "Stacks"}
    ]
    mathlib, = (p for p in manifest["packages"] if p["name"] == "mathlib")
    mathlib["inherited"] = False
    manifest["name"] = "erdos782_challenge"
    (directory / "lake-manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8",
    )
    (directory / "lakefile.toml").write_text(
        'name = "erdos782_challenge"\n'
        '[[require]]\nname = "mathlib"\nscope = "leanprover-community"\n'
        f'git = {json.dumps(mathlib["url"])}\nrev = {json.dumps(mathlib["rev"])}\n'
        '[[lean_lib]]\nname = "Comparator"\nglobs = ["Comparator.+"]\n',
        encoding="utf-8",
    )


def check_export(solution, command):
    with TemporaryDirectory(prefix="erdos782-challenge-") as temp:
        challenge = Path(temp)
        prepare_challenge(challenge)
        run("cache.log", [
            "lake", "exe", "cache", "get",
            "Mathlib.Algebra.Group.Even", "Mathlib.Data.Set.Defs",
        ], cwd=challenge)
        run("build.log", ["lake", "build", "Comparator.Challenge"], cwd=challenge)
        check = challenge / "Check.lean"
        check.write_text(
            "import Comparator.Challenge\n"
            "example : ¬ Erdos782.FCPartIStatement := Erdos782.erdos_782.parts.i_neg\n"
            "#check @Erdos782.erdos_782.parts.i_neg\n",
            encoding="utf-8",
        )
        run("statement.log", ["lake", "env", "lean", str(check)], cwd=challenge)
        log = run("fc-target.log", command + ["--solution-from-export", str(solution)], cwd=challenge)
        run("replay.log", ["lake", "env", "leanchecker", "--from-export", str(solution)], cwd=challenge)
        (RESULTS / "replay-status.txt").write_text("PASS\n", encoding="utf-8")
        return log


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--trusted-local", action="store_true",
        help="Run this trusted checkout without Lake's Linux bubblewrap sandbox",
    )
    parser.add_argument(
        "--solution-export", type=Path,
        help="Compare a Lean NDJSON proof export against a freshly built challenge",
    )
    args = parser.parse_args()

    RESULTS.mkdir(exist_ok=True)
    for receipt in ("result.json", "replay-status.txt"):
        (RESULTS / receipt).unlink(missing_ok=True)
    command = ["lake", "env", "lake", "comparator"]
    if args.trusted_local:
        command.append("--inadvisably-no-sandbox")
    if args.solution_export:
        log = check_export(args.solution_export.resolve(strict=True), command)
    else:
        run("build.log", ["lake", "build", "Comparator.Challenge", "Comparator.Candidate"])
        run("statement.log", ["lake", "env", "lean", "../verification/Check.lean"])
        log = run("fc-target.log", command)
    if any(verdict not in log for verdict in VERDICTS):
        raise SystemExit("Comparator did not report acceptance by both kernels.")

    config = json.loads((LEAN / "comparator.json").read_text(encoding="utf-8"))
    receipt = {
        "accepted": True,
        "targets": config["theorem_names"],
        "kernels": ["Lean", "nanoda"],
        "lake_bubblewrap": not args.trusted_local,
        "scope": "unconditional negation of the pinned FC 782(i) proposition",
        "solution_input": "proof export" if args.solution_export else "Lean source",
    }
    (RESULTS / "result.json").write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8",
    )


if __name__ == "__main__":
    main()
