"""Package only the compiled module files needed to regenerate a Lean export."""

import json
from pathlib import Path
import subprocess
import sys
import tarfile


inputs, output = map(Path, sys.argv[1:])
with inputs.open() as files, subprocess.Popen(
    ["zstd", "-T2", "-1", "-o", str(output)], stdin=subprocess.PIPE
) as compressor:
    with tarfile.open(fileobj=compressor.stdin, mode="w|") as archive:
        for line in files:
            destination, source = json.loads(line)
            archive.add(source, arcname=destination, recursive=False)
    compressor.stdin.close()
    if compressor.wait():
        raise SystemExit("Could not compress the compiled export inputs.")
