"""Plan and build the missing AxiomMath dependency modules in topological waves."""

import argparse
from functools import lru_cache
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[1]
START = "Mordell.MordellConjecture.FunctionField"
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (?:all )?(\w[.\w]+)", re.M)
PACKAGES = {
    "Mordell": "Mordell",
    "Stacks": "Stacks",
    "StacksCore": "Stacks",
    "StacksFrontier": "Stacks",
}
CUTOFFS = (2, 4, 8, 16, 27, 45)
SHARDS = 6


def package(module):
    return PACKAGES.get(module.split(".", 1)[0])


def local_module(module):
    return Path(*module.split("."))


def make_plan(packages, built_packages):
    @lru_cache(None)
    def imports(module):
        source = packages / package(module) / local_module(module).with_suffix(".lean")
        return tuple(imp for imp in IMPORT.findall(source.read_text()) if package(imp))

    seen = set()
    pending = [START]
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(imports(module))

    missing = {
        mod for mod in seen
        if not (built_packages / package(mod) / ".lake/build/lib/lean"
                / local_module(mod).with_suffix(".olean")).is_file()
    }

    @lru_cache(None)
    def depth(module):
        return 1 + max((depth(imp) for imp in imports(module) if imp in missing), default=0)

    waves = [[] for _ in range(len(CUTOFFS) + 1)]
    for module in sorted(missing):
        index = sum(depth(module) > cutoff for cutoff in CUTOFFS)
        waves[index].append(module)

    plan = []
    for wave in waves:
        modules = set(wave)
        roots = modules - {imp for mod in modules for imp in imports(mod) if imp in modules}

        @lru_cache(None)
        def required(module):
            result = {module}
            for imp in imports(module):
                if imp in modules:
                    result.update(required(imp))
            return result

        shards = [{"targets": [], "modules": set()} for _ in range(SHARDS)]
        for target in sorted(roots, key=lambda mod: (-len(required(mod)), mod)):
            inputs = required(target)
            choice = min(shards, key=lambda s: len(s["modules"] | inputs))
            choice["targets"].append(target)
            choice["modules"].update(inputs)
        for shard in shards:
            shard["modules"] = sorted(shard["modules"])
        plan.append([s for s in shards if s["targets"]] or [{"modules": [], "targets": []}])
    return plan


def compile_shard(lean, plan, wave, shard, output):
    work = plan[wave][shard]
    if work["targets"]:
        subprocess.run(["lake", "build", *("+" + target for target in work["targets"])],
                       cwd=lean, check=True)
    packages = lean / ".lake/packages"
    archive = output / f"wave-{wave}-shard-{shard}.tar.zst"
    output.mkdir(parents=True, exist_ok=True)
    with subprocess.Popen(["zstd", "-T2", "-3", "-o", str(archive)], stdin=subprocess.PIPE) as zstd:
        with tarfile.open(fileobj=zstd.stdin, mode="w|") as tar:
            for module in work["modules"]:
                build = packages / package(module) / ".lake/build"
                rel = local_module(module)
                proof = build / "lib/lean" / rel.with_suffix(".olean")
                if not proof.is_file():
                    raise RuntimeError(f"Build output missing for {module}")
                for tree in (build / "lib/lean", build / "ir"):
                    for path in sorted((tree / rel.parent).glob(rel.name + ".*")):
                        if path.is_file() and not path.name.endswith(".setup.json"):
                            tar.add(path, arcname=path.relative_to(packages), recursive=False)
        zstd.stdin.close()
        if zstd.wait():
            raise RuntimeError(f"Could not compress {archive}")
    print(f"Packed compiler outputs for {len(work['modules'])} modules.")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--lean", type=Path, default=ROOT / "lean")
    sub = cli.add_subparsers(dest="command", required=True)
    prepare = sub.add_parser("plan")
    prepare.add_argument("output", type=Path)
    prepare.add_argument("--built-packages", type=Path)
    build = sub.add_parser("build")
    build.add_argument("plan", type=Path)
    build.add_argument("wave", type=int)
    build.add_argument("shard", type=int)
    build.add_argument("output", type=Path)
    args = cli.parse_args()
    if args.command == "plan":
        packages = args.lean / ".lake/packages"
        plan = make_plan(packages, args.built_packages or packages)
        args.output.write_text(json.dumps(plan) + "\n")
        for wave, shards in enumerate(plan):
            print(f"wave{wave}={json.dumps(list(range(len(shards))))}")
        print("Modules by wave and shard:", [[len(s["modules"]) for s in w] for w in plan],
              file=sys.stderr)
    else:
        compile_shard(args.lean, json.loads(args.plan.read_text()),
                      args.wave, args.shard, args.output)


if __name__ == "__main__":
    main()
