#!/usr/bin/env bash
# Export the theorem and the kernel primitives compared by Lake 4.35.0.
set -euo pipefail

output="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
cd "$(dirname "$0")/../lean"

lake env leanexport Comparator.Candidate -- \
  Quot Quot.mk Quot.lift Quot.ind Erdos782.erdos_782.parts.i_neg \
  propext Classical.choice Quot.sound \
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble \
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat \
  List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam \
  | gzip -n -1 > "$output"
