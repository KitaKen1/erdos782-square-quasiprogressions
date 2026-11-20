#!/usr/bin/env bash
# Export the theorem and the kernel primitives compared by Lake 4.35.0.
set -euo pipefail

module=Comparator.Candidate
if [[ "${1:-}" == --challenge ]]; then
  module=Comparator.Challenge
  shift
fi
compiled_root=''
if [[ "${1:-}" == --compiled-root ]]; then
  compiled_root="$(cd "$2" && pwd)"
  shift 2
fi
raw=false
if [[ "${1:-}" == --raw ]]; then
  raw=true
  shift
fi
if [[ "$#" != 1 ]]; then
  echo "Usage: $0 [--challenge] [--compiled-root DIRECTORY] [--raw] OUTPUT" >&2
  exit 2
fi
output="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
cd "$(dirname "$0")/../lean"

export_proof() {
  local command=(lake env leanexport)
  if [[ -n "$compiled_root" ]]; then
    command=(env "LEAN_PATH=$compiled_root" "$(lean --print-prefix)/bin/leanexport")
  fi
  "${command[@]}" "$module" -- \
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
