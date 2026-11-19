"""Add a bounded-memory mode to the NDJSON parser from the pinned Lean toolchain."""

import hashlib
from pathlib import Path
import subprocess


PARSER_SHA256 = "ff46b43893ad39bc8d8b71e2b028b1d7c7065ac11efbeea368d1641419f9460e"


def replace(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f"Unexpected upstream parser near {old!r}")
    return source.replace(old, new, 1)


def main():
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    source = (prefix / "src/lean/LeanExport/Parse.lean").read_bytes()
    if hashlib.sha256(source).hexdigest() != PARSER_SHA256:
        raise ValueError("The split parser requires the pinned Lean 4.35.0 source")
    source = source.decode().split("end Parse\n", 1)[0]
    source = replace(source, "public import Lean.Declaration", "public import Lean.Environment")
    source = replace(source, "namespace LeanExport", "namespace ExportReplay")
    source = replace(source, "public structure ExportedEnv where\n  constMap : Std.HashMap Lean.Name Lean.ConstantInfo\n  constOrder : Array Lean.Name\n  deriving Inhabited\n\n", "")
    source = replace(source, "  constOrder : Array Lean.Name := #[]", """  constOrder : Array Lean.Name := #[]
  declared : NameHashSet := {}
  -- All expression IDs are consecutive. The first pass records the number of the last
  -- input line that references each expression, using zero for an unused expression.
  uses : Array UInt32 := #[]
  lineNumber : UInt32 := 1
  indexing : Bool := false
  finishedExpressions : Array Nat := #[]""")
    source = replace(source, """  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  return e""", """  if (← get).indexing then
    let found ← modifyGet fun s =>
      if eidx < s.uses.size then
        (true, { s with uses := s.uses.set! eidx s.lineNumber })
      else
        (false, s)
    unless found do fail s!"Unknown expression {eidx}"
    return mkSort .zero
  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  if (← get).uses[eidx]! == (← get).lineNumber then
    modify fun s => { s with finishedExpressions := s.finishedExpressions.push eidx }
  return e""")
    source = replace(source, """  if (← get).exprMap.contains eidx then
    fail s!"Expr index {eidx} bound twice"
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }""", """  if (← get).indexing then
    unless eidx == (← get).uses.size do fail s!"Nonconsecutive expression index {eidx}"
    modify fun s => { s with uses := s.uses.push 0 }
  else if (← get).uses[eidx]! != 0 then
    modify fun s => { s with exprMap := s.exprMap.insert eidx e }""")
    source = replace(source, """  if (← get).constMap.contains name then
    fail s!"Duplicate declaration: {name}"
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }""", """  if (← get).indexing then return
  if (← get).declared.contains name then
    fail s!"Duplicate declaration: {name}"
  modify fun s => {
    s with
      declared := s.declared.insert name
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }""")
    start = source.index("partial def parseItems")
    source = source[:start]
    source += Path("ParserDriver.lean.part").read_text()
    Path("ExportReplayParser.lean").write_text(source)


if __name__ == "__main__":
    main()
