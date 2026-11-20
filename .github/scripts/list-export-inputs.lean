import Lean

open Lean System

def main (args : List String) : IO Unit := do
  let sysroot ← findSysroot
  let builtinPrefix := (← realPathNormalized (← getLibDir sysroot)).toString ++ "/"
  initSearchPath sysroot
  let mut pending := args.toArray.map String.toName
  let mut seen : NameHashSet := {}
  let mut files := 0
  while let some mod := pending.back? do
    pending := pending.pop
    if seen.contains mod then continue
    seen := seen.insert mod
    let path ← realPathNormalized (← findOLean mod)
    if path.toString.startsWith builtinPrefix then continue
    let (header, _) ← readModuleData path
    pending := pending ++ header.imports.map (·.module)
    let relative := modToFilePath "." mod "olean"
    let parts := if header.isModule then
      #[(relative, path),
        (OLeanLevel.server.adjustFileName relative, OLeanLevel.server.adjustFileName path),
        (OLeanLevel.private.adjustFileName relative, OLeanLevel.private.adjustFileName path)]
      else #[(relative, path)]
    for (destination, source) in parts do
      unless ← source.pathExists do
        throw (IO.userError s!"Missing compiled export input '{source}'")
      IO.println (toJson (destination.toString, source.toString)).compress
      files := files + 1
  IO.eprintln s!"Found {files} compiled export inputs."
