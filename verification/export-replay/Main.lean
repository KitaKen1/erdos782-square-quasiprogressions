import ExportReplayParser
import Lean.Replay
import Lean.Util.Path
import Lean.Util.FoldConsts
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

private def sliceRange (declarations : Array ConstantInfo) (part parts : Nat)
    (subSlice : Option (Nat × Nat)) : IO (Nat × Nat × String) := do
  let bounds ← sliceBoundaries declarations parts
  unless part < parts do throw (IO.userError "Invalid slice index")
  let start := bounds[part]!
  let stop := bounds[part + 1]!
  match subSlice with
    | none => pure (start, stop, toString part)
    | some (subPart, subParts) => do
      unless subPart < subParts do throw (IO.userError "Invalid nested slice index")
      let offsets ← sliceBoundaries (declarations.extract start stop) subParts
      pure (start + offsets[subPart]!, start + offsets[subPart + 1]!, s!"{part}-{subPart}")

private def checkSlice (directory scratch : System.FilePath) (index part parts : Nat)
    (subSlice : Option (Nat × Nat) := none) : IO Unit := do
  let data ← getChunk directory index
  let (lo, hi, label) ← sliceRange data.constants part parts subSlice
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

private structure ProofPrefix where
  declarations : Std.HashMap Name (Nat × ConstantInfo) := {}
  nextIndex : Nat := 0

private def ProofPrefix.append (prior : ProofPrefix) (declarations : Array ConstantInfo) :
    ProofPrefix :=
  declarations.foldl (fun state ci =>
    { declarations := state.declarations.insert ci.name (state.nextIndex, ci)
      nextIndex := state.nextIndex + 1 }) prior

private def readProofPrefix (directory : System.FilePath) (chunk : Nat) : IO ProofPrefix := do
  let mut prior : ProofPrefix := {}
  for index in [:chunk] do
    prior := prior.append (← getChunk directory index).constants
  return prior

private def opaqueView (ci : ConstantInfo) : ConstantInfo :=
  match ci with
  | .defnInfo value => .opaqueInfo {
      name := value.name, levelParams := value.levelParams, type := value.type
      value := value.value, isUnsafe := value.safety != .safe, all := value.all }
  | _ => ci

private def projectionUses (ci : ConstantInfo) : Array Name :=
  match ci with
  | .opaqueInfo _ | .thmInfo _ => ci.type.getUsedConstants
  | .recInfo info =>
    info.rules.foldl (fun names rule => names ++ #[rule.ctor] ++ rule.rhs.getUsedConstants)
      ci.getUsedConstantsAsSet.toList.toArray
  | .inductInfo info => ci.getUsedConstantsAsSet.toList.toArray ++ info.all.toArray
  | .ctorInfo info => ci.getUsedConstantsAsSet.toList.toArray.push info.induct
  | _ => ci.getUsedConstantsAsSet.toList.toArray

private def implicitPrimitives : Array Name :=
  primitives ++ #[`Nat.zero, `Nat.succ, `List.nil, `List.cons]

-- The witness only controls unfolding. Every type and value comes from the
-- original export, and dependencies outside the current block must precede it.
private def projectedImports (prior : ProofPrefix) (target : Array ConstantInfo)
    (transparent : Nat → Name → Bool) (additional : Array Name := #[])
    (preferUnfold : Array Name := #[]) :
    IO (Array ConstantInfo × Array Nat) := do
  let localNames := target.foldl (fun (s : NameHashSet) ci => s.insert ci.name) {}
  let base := implicitPrimitives.filter prior.declarations.contains
  let mut pending := target.foldl (fun names ci => names ++ ci.getUsedConstantsAsSet.toList.toArray)
    (base ++ additional)
  let mut seen := localNames
  let mut imports := #[]
  let mut unfolded := #[]
  while let some name := pending.back? do
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some (index, ci) := prior.declarations[name]? |
      throw (IO.userError s!"Missing earlier declaration '{name}'")
    let projected := match ci with
      | .defnInfo defn =>
        if preferUnfold.contains name then
          -- Abbreviations and regular definitions admit the same kernel
          -- reduction. This only gives an already checked wrapper priority.
          match defn.hints with
          | .regular _ => .defnInfo { defn with hints := .abbrev }
          | _ => ci
        else if base.contains name || transparent index name then ci else opaqueView ci
      | _ => ci
    if projected.isDefinition then unfolded := unfolded.push index
    imports := imports.push projected
    pending := pending ++ projectionUses projected
  return (imports, unfolded)

private structure ProjectionBlock where
  stop : Nat
  unfold : Array Nat
  prefer : Option (Array String) := none
  deriving ToJson, FromJson

private structure SourceBlock where
  stop : Nat
  owner : String
  deriving ToJson, FromJson

private structure SourceModule where
  usesModule : Bool
  imports : Array Import
  exportedDefs : NameHashSet

private def loadSourceModule (cache : Std.HashMap Name SourceModule) (owner : Name) :
    IO (SourceModule × Std.HashMap Name SourceModule) := do
  if let some source := cache[owner]? then return (source, cache)
  let (data, _) ← readModuleData (← findOLean owner)
  let source : SourceModule := {
    usesModule := data.isModule
    imports := data.imports
    exportedDefs := data.constants.foldl
      (fun (names : NameHashSet) ci => if ci.isDefinition then names.insert ci.name else names) {} }
  return (source, cache.insert owner source)

private def moduleScope (cache : Std.HashMap Name SourceModule) (owner : Name) :
    IO (Std.HashMap Name Bool × Std.HashMap Name SourceModule) := do
  let (root, initialCache) ← loadSourceModule cache owner
  let mut cache := initialCache
  let mut levels : Std.HashMap Name Bool := {}
  let mut pending := #[(owner, true)]
  while let some (next, all) := pending.back? do
    pending := pending.pop
    if let some previous := levels[next]? then
      if previous || !all then continue
    levels := levels.insert next all
    let (info, updated) ← loadSourceModule cache next
    cache := updated
    for imp in info.imports do
      if all || imp.isExported || !root.usesModule then
        pending := pending.push (imp.module, !root.usesModule || (all && imp.importAll))
  return (levels, cache)

private def loadOrigins (env : Environment) (prior : ProofPrefix) :
    Std.HashMap Name Name := Id.run do
  let modules := env.allImportedModuleNames
  let mut origins := {}
  for (name, _) in prior.declarations.toList do
    if let some idx := env.getModuleIdxFor? name then
      origins := origins.insert name modules[idx.toNat]!
  return origins

private def admissibleCut (declarations : Array ConstantInfo) (cut : Nat) : Bool :=
  cut == 0 || cut == declarations.size ||
    !(isGroupedDeclaration declarations[cut - 1]! && isGroupedDeclaration declarations[cut]!)

private def generateProjectionPlan (visible : Environment) (directory : System.FilePath)
    (index start : Nat) (layoutPath : System.FilePath) : IO (Array ProjectionBlock) := do
  let data ← getChunk directory index
  let layoutJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile layoutPath)
  let layout : Array SourceBlock ← IO.ofExcept <| fromJson? layoutJson
  let some final := layout.back? | throw (IO.userError "Empty projection layout")
  unless start < final.stop && final.stop ≤ data.constants.size do
    throw (IO.userError "Invalid end of the projection layout")
  let mut prior := (← readProofPrefix directory index).append (data.constants.extract 0 start)
  let origins := loadOrigins visible (prior.append (data.constants.extract start final.stop))
  let mut startOffset := start
  let mut plan : Array ProjectionBlock := #[]
  let mut scopes : Std.HashMap Name (Std.HashMap Name Bool) := {}
  let mut modules : Std.HashMap Name SourceModule := {}
  let mut pending := #[]
  for spec in layout do
    unless startOffset < spec.stop && spec.stop ≤ data.constants.size do
      throw (IO.userError "Invalid source block")
    let owner := spec.owner.toName
    if !scopes.contains owner then
      let (scope, updated) ← moduleScope modules owner
      scopes := scopes.insert owner scope
      modules := updated
    pending := pending.push owner
    if !admissibleCut data.constants spec.stop then continue
    let localContexts := pending.map (scopes[·]!)
    let (_, unfolds) ← projectedImports prior (data.constants.extract startOffset spec.stop) (fun _ name =>
      match origins[name]? with
      | none => false
      | some owner => localContexts.any fun scope =>
        match scope[owner]? with
        | none => false
        | some true => true
        | some false => (modules[owner]?.any fun info => info.exportedDefs.contains name))
    plan := plan.push { stop := spec.stop, unfold := unfolds }
    prior := prior.append (data.constants.extract startOffset spec.stop)
    startOffset := spec.stop
    pending := #[]
  unless pending.isEmpty do throw (IO.userError "Plan ends inside a declaration package")
  return plan

private structure ProjectionRequest where
  chunk : Nat
  start : Nat
  layout : String
  output : String
  deriving FromJson

private def generateProjectionPlans (directory requestsPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  let requestsJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile requestsPath)
  let requests : Array ProjectionRequest ← IO.ofExcept <| fromJson? requestsJson
  IO.eprintln "Reading the compiled modules to recover their visibility data"
  let visible ← importModules #[{ module := `Comparator.Candidate }] {}
  for job in requests do
    let plan ← generateProjectionPlan visible directory job.chunk job.start ⟨job.layout⟩
    IO.FS.writeFile ⟨job.output⟩ ((toJson plan).compress ++ "\n")
    IO.eprintln s!"Wrote {plan.size} projection blocks to {job.output}"

private def unavailableConstant (error : IO.Error) (prior : ProofPrefix) : Option Name := do
  let [_, tail] := error.toString.splitOn "(kernel) unknown constant '" | none
  let first ← (tail.splitOn "\n").head?
  unless first.endsWith "'" do none
  let rendered := (first.dropEnd 1).toString
  let simple := rendered.toName
  if prior.declarations.contains simple then
    return simple
  let (name, _) ← prior.declarations.toList.find? fun (name, _) => name.toString == rendered
  return name

private unsafe def checkProjectionBlock (scratch : System.FilePath) (prior : ProofPrefix)
    (target : Array ConstantInfo) (block : ProjectionBlock) : IO Unit := do
  let unfolded := block.unfold.foldl (fun (s : Std.HashSet Nat) n => s.insert n) {}
  let preference := (block.prefer.getD #[]).map String.toName
  let mod := `ProjectedExportContext
  let file := scratch / "ProjectedExportContext.olean"
  searchPathRef.set [scratch]
  let mut additional := #[]
  repeat
    let (declarations, _) ← projectedImports prior target (fun index _ => unfolded.contains index)
      additional preference
    saveModuleData file mod {
      isModule := false, imports := #[],
      constNames := declarations.map ConstantInfo.name, constants := declarations,
      extraConstNames := #[], entries := #[] }
    try
      withImportModules #[{ module := mod }] {} fun env => checkDeclarations env target
      IO.FS.removeFile file
      return
    catch error =>
      let some name := unavailableConstant error prior | throw error
      if additional.contains name || declarations.any (·.name == name) then throw error
      additional := additional.push name

private unsafe def checkProjectedSlice (directory scratch : System.FilePath) (index part parts : Nat)
    (subPart subParts : Nat) (planPath : System.FilePath) : IO Unit := do
  let data ← getChunk directory index
  let (lo, hi, label) ← sliceRange data.constants part parts (some (subPart, subParts))
  let planJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile planPath)
  let plan : Array ProjectionBlock ← IO.ofExcept <| fromJson? planJson
  let mut prior := (← readProofPrefix directory index).append (data.constants.extract 0 lo)
  let mut start := lo
  for block in plan do
    unless start < block.stop && block.stop ≤ hi && admissibleCut data.constants block.stop do
      throw (IO.userError "Incomplete or invalid declaration range in projection plan")
    let target := data.constants.extract start block.stop
    checkProjectionBlock scratch prior target block
    IO.eprintln s!"Lean checked export declarations {start} to {block.stop} in a restricted environment"
    prior := prior.append target
    start := block.stop
  unless start == hi do throw (IO.userError "Projection plan did not cover the entire slice")
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

unsafe def main (args : List String) : IO Unit := do
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
  | ["check-projection", directory, scratch, index, part, parts, subPart, subParts, plan] =>
    let some index := index.toNat? | throw (IO.userError "Expected a chunk index")
    let some part := part.toNat? | throw (IO.userError "Expected a slice index")
    let some subPart := subPart.toNat? | throw (IO.userError "Expected a nested slice index")
    checkProjectedSlice ⟨directory⟩ ⟨scratch⟩ index part (← positive parts)
      subPart (← positive subParts) ⟨plan⟩
  | ["make-projections", directory, requests] =>
    generateProjectionPlans ⟨directory⟩ ⟨requests⟩
  | ["compare", directory, count, challenge] =>
    compareProof ⟨directory⟩ (← positive count) ⟨challenge⟩
  | _ =>
    throw (IO.userError "Usage: export-replay split PROOF NEW_DIRECTORY BATCH_LINES | check DIRECTORY INDEX | check-slice DIRECTORY SCRATCH INDEX PART PARTS [SUB_PART SUB_PARTS] | compare DIRECTORY COUNT CHALLENGE")
