"""Extract the exact statement and definition of part (i) from pinned FC source."""

from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / "verification/reference/782.lean"
REFERENCE_SHA256 = "0a2cff2f5c38d9e756c749ee41f27bfbff5c7a6105c1c8be3ec0fd1c42a1ef5d"
COMPARATOR = ROOT / "lean/Comparator"


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check the generated file and targets")
    args = parser.parse_args()

    source = REFERENCE.read_bytes()
    if sha256(source).hexdigest() != REFERENCE_SHA256:
        raise SystemExit("The FC snapshot differs from the pinned source.")
    definition, = re.findall(
        r"^def ContainsQuasiProgression .+?(?=\n\n)", source.decode(), re.M | re.S,
    )
    statement, = re.findall(
        r"^theorem erdos_782\.parts\.i :\n(.+?) := by\n  sorry$", source.decode(), re.M | re.S,
    )
    generated = (
        "-- Generated from FormalConjectures/ErdosProblems/782.lean.\n"
        "-- Copyright 2026 The Formal Conjectures Authors. Licensed under Apache-2.0.\n"
        "-- FC revision 2de491f90132d3f3fac934edf5bd72acb3dfd15c.\n"
        "module\n\n"
        "public import Mathlib.Algebra.Group.Even\n"
        "public import Mathlib.Data.Set.Defs\n\n"
        "@[expose] public section\n\n"
        "namespace Erdos782\n\n"
        f"{definition}\n\n"
        "/-- The type of FC's erdos_782.parts.i, captured without its proof. -/\n"
        f"abbrev FCPartIStatement : Prop :=\n{statement}\n\n"
        "end Erdos782\n"
    )
    output = COMPARATOR / "FCStatement.lean"
    if not args.check:
        output.write_text(generated, encoding="utf-8")
        return
    if output.read_text(encoding="utf-8") != generated:
        raise SystemExit(f"{output.name} differs from the generated FC statement.")

    for name in ("Challenge.lean", "Candidate.lean"):
        targets = re.findall(
            r"^theorem erdos_782\.parts\.i_neg :\n    ¬ \((.+?)\) :=",
            (COMPARATOR / name).read_text(encoding="utf-8"), re.M | re.S,
        )
        if len(targets) != 1 or targets[0].split() != statement.split():
            raise SystemExit(f"{name} must negate the exact FC proposition without arguments.")
    print("Both Comparator targets negate the pinned FC proposition verbatim.")


if __name__ == "__main__":
    main()
