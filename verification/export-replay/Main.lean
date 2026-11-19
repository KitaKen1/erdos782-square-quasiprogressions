import ExportReplayParser
import Lean.Replay
import Lean.Util.Path
import LeanExport.Parse
import Lake.Check.Compare

open Lean

private def chunkName (index : Nat) : Name :=
  Name.mkSimple s!"ExportReplayChunk{index}"

private def sourceTarget : Name := `Erdos782.erdos_782.parts.i_neg

private def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def quotientGenerated : Array Name :=
  #[`Quot.mk, `Quot.lift, `Quot.ind]

-- Match the primitive declarations checked by the pinned Lake Comparator.
private def primitives : Array Name :=
  #[`Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div, `Nat.mod, `Nat.beq, `Nat.ble,
    `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight, `String.ofList, `Char.ofNat,
    `List, `eagerReduce, `Nat, `String, `String.mk, `Char, `optParam, `autoParam, `semiOutParam,
    `outParam, `Quot, `Quot.mk, `Quot.lift, `Quot.ind]

private def getChunk (directory : System.FilePath) (index : Nat) : IO ModuleData := do
  let (data, _) ← readModuleData (directory / (s!"{chunkName index}.olean"))
  let expectedImports : Array Import :=
    if index == 0 then #[] else #[{ module := chunkName (index - 1) }]
  unless data.imports == expectedImports && data.entries.isEmpty && data.extraConstNames.isEmpty &&
      data.constNames == data.constants.map ConstantInfo.name do
    throw (IO.userError s!"Invalid module data in chunk {index}")
  return data

private def checkChunk (directory : System.FilePath) (index : Nat) : IO Unit := do
  -- Only the preceding, same-export chunks can be imported. Each is checked in a
  -- separate invocation, so success of this worker is conditional upon their checks.
  searchPathRef.set [directory]
  let data ← getChunk directory index
  let imported ←
    if index == 0 then mkEmptyEnvironment else importModules data.imports {}
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for ci in data.constants do
    if ci.isUnsafe || ci.isPartial then
      throw (IO.userError s!"Unsafe or partial declaration '{ci.name}'")
    if (imported.find? ci.name).isSome || constants.contains ci.name then
      throw (IO.userError s!"Duplicate declaration '{ci.name}'")
    if let .axiomInfo axiomInfo := ci then
      unless allowedAxioms.contains axiomInfo.name do
        throw (IO.userError s!"Unpermitted axiom '{axiomInfo.name}'")
    unless quotientGenerated.contains ci.name do
      constants := constants.insert ci.name ci
  let checked ← imported.toKernelEnv.replay constants
  for ci in data.constants do
    unless checked.find? ci.name == some ci do
      throw (IO.userError s!"Kernel replay produced different information for '{ci.name}'")
  IO.println s!"Lean kernel accepted chunk {index} ({data.constants.size} declarations)"

private def compareProof (directory : System.FilePath) (count : Nat)
    (challengePath : System.FilePath) : IO Unit := do
  let challenge ← IO.FS.withFile challengePath .read fun handle =>
    LeanExport.parseStream (.ofHandle handle)
  let mut needed : Std.HashMap Name ConstantInfo := {}
  for index in [:count] do
    for ci in (← getChunk directory index).constants do
      if challenge.constMap.contains ci.name then
        if needed.contains ci.name then
          throw (IO.userError s!"Duplicate exported declaration '{ci.name}'")
        needed := needed.insert ci.name ci
  let candidate : LeanExport.ExportedEnv := { constMap := needed, constOrder := #[] }
  IO.ofExcept <| Lake.Check.compareAt challenge candidate (#[sourceTarget] ++ allowedAxioms) #[] primitives
  IO.println "The theorem statement and primitives match the pinned FC challenge"

private def positive (text : String) : IO Nat := do
  if let some n := text.toNat? then
    if n > 0 then return n
  throw (IO.userError "Expected a positive integer")

def main (args : List String) : IO Unit := do
  match args with
  | ["split", proof, directory, batchSize] =>
    let path : System.FilePath := ⟨directory⟩
    if ← path.pathExists then
      throw (IO.userError "Use a new output directory")
    IO.FS.createDirAll path
    let count ← ExportReplay.splitFile ⟨proof⟩ path (← positive batchSize)
    if count == 0 then throw (IO.userError "The export contains no declarations")
    IO.FS.writeFile (path / "count") s!"{count}\n"
  | ["check", directory, index] =>
    let some index := index.toNat? | throw (IO.userError "Expected a chunk index")
    checkChunk ⟨directory⟩ index
  | ["compare", directory, count, challenge] =>
    compareProof ⟨directory⟩ (← positive count) ⟨challenge⟩
  | _ =>
    throw (IO.userError "Usage: export-replay split PROOF NEW_DIRECTORY BATCH_LINES | check DIRECTORY INDEX | compare DIRECTORY COUNT CHALLENGE")
