#!/usr/bin/env bash
# Export the theorem and the kernel primitives compared by Lake 4.35.0.
set -euo pipefail

module=Comparator.Candidate
if [[ "${1:-}" == --challenge ]]; then
  module=Comparator.Challenge
  shift
fi
raw=false
if [[ "${1:-}" == --raw ]]; then
  raw=true
  shift
fi
if [[ "$#" != 1 ]]; then
  echo "Usage: $0 [--challenge] [--raw] OUTPUT" >&2
  exit 2
fi
output="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
cd "$(dirname "$0")/../lean"

export_proof() {
  lake env leanexport "$module" -- \
    Quot Quot.mk Quot.lift Quot.ind Erdos782.erdos_782.parts.i_neg \
    propext Classical.choice Quot.sound \
    Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble \
    Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat \
    List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam
}

if [[ "$raw" == true ]]; then
  export_proof > "$output"
else
  export_proof | gzip -n -1 > "$output"
fi
