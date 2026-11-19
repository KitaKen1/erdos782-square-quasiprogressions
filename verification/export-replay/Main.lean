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

private def checkDeclarations (imported : Environment) (declarations : Array ConstantInfo) :
    IO Unit := do
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for ci in declarations do
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
  for ci in declarations do
    unless checked.find? ci.name == some ci do
      throw (IO.userError s!"Kernel replay produced different information for '{ci.name}'")

private def checkChunk (directory : System.FilePath) (index : Nat) : IO Unit := do
  -- Only the preceding, same-export chunks can be imported. Each is checked in a
  -- separate invocation, so success of this worker is conditional upon their checks.
  searchPathRef.set [directory]
  let data ← getChunk directory index
  let imported ←
    if index == 0 then mkEmptyEnvironment else importModules data.imports {}
  checkDeclarations imported data.constants
  IO.println s!"Lean kernel accepted chunk {index} ({data.constants.size} declarations)"

private def isGroupedDeclaration : ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
  | _ => false

-- Move cuts that fall inside an inductive or quotient package to the end of that package.
private def sliceBoundaries (declarations : Array ConstantInfo) (parts : Nat) :
    IO (Array Nat) := do
  let size := declarations.size
  unless 0 < parts && parts ≤ size do
    throw (IO.userError "Invalid slice count")
  let mut bounds : Array Nat := #[0]
  for i in [1:parts] do
    let mut cut := i * size / parts
    while cut < size && isGroupedDeclaration declarations[cut - 1]! &&
        isGroupedDeclaration declarations[cut]! do
      cut := cut + 1
    unless bounds.back! < cut && cut < size do
      throw (IO.userError "Could not split into nonempty declaration slices")
    bounds := bounds.push cut
  return bounds.push size

private def checkSlice (directory scratch : System.FilePath) (index part parts : Nat)
    (subSlice : Option (Nat × Nat) := none) : IO Unit := do
  let data ← getChunk directory index
  let bounds ← sliceBoundaries data.constants parts
  unless part < parts do throw (IO.userError "Invalid slice index")
  let start := bounds[part]!
  let stop := bounds[part + 1]!
  let (lo, hi, label) ← match subSlice with
    | none => pure (start, stop, toString part)
    | some (subPart, subParts) => do
      unless subPart < subParts do throw (IO.userError "Invalid nested slice index")
      let offsets ← sliceBoundaries (data.constants.extract start stop) subParts
      pure (start + offsets[subPart]!, start + offsets[subPart + 1]!, s!"{part}-{subPart}")
  let mut imports := data.imports
  searchPathRef.set [scratch, directory]
  if lo > 0 then
    -- This prefix consists only of the declarations preceding this slice in the
    -- original hashed chunk. Each prefix declaration has its own kernel check.
    let mod := `ExportReplaySlicePrefix
    let prefixDeclarations := data.constants.extract 0 lo
    let prefixData : ModuleData := { data with
      constants := prefixDeclarations
      constNames := prefixDeclarations.map ConstantInfo.name
    }
    saveModuleData (scratch / "ExportReplaySlicePrefix.olean") mod prefixData
    imports := #[{ module := mod }]
  let imported ←
    if imports.isEmpty then mkEmptyEnvironment else importModules imports {}
  checkDeclarations imported (data.constants.extract lo hi)
  IO.println s!"Lean kernel accepted chunk {index}, slice {label} ({lo} to {hi} of {data.constants.size} declarations)"

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
  | ["check-slice", directory, scratch, index, part, parts] =>
    let some index := index.toNat? | throw (IO.userError "Expected a chunk index")
    let some part := part.toNat? | throw (IO.userError "Expected a slice index")
    checkSlice ⟨directory⟩ ⟨scratch⟩ index part (← positive parts)
  | ["check-slice", directory, scratch, index, part, parts, subPart, subParts] =>
    let some index := index.toNat? | throw (IO.userError "Expected a chunk index")
    let some part := part.toNat? | throw (IO.userError "Expected a slice index")
    let some subPart := subPart.toNat? | throw (IO.userError "Expected a nested slice index")
    checkSlice ⟨directory⟩ ⟨scratch⟩ index part (← positive parts) (some (subPart, ← positive subParts))
  | ["compare", directory, count, challenge] =>
    compareProof ⟨directory⟩ (← positive count) ⟨challenge⟩
  | _ =>
    throw (IO.userError "Usage: export-replay split PROOF NEW_DIRECTORY BATCH_LINES | check DIRECTORY INDEX | check-slice DIRECTORY SCRATCH INDEX PART PARTS [SUB_PART SUB_PARTS] | compare DIRECTORY COUNT CHALLENGE")
