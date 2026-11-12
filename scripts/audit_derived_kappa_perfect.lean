import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedKappaPerfectAll
import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedKappaCoversAll
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Closure,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Equivalence,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Inclusion,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Input,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.CompactStage,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.TelescopeSplitting,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.RepresentativeImage,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.HomotopyRetract,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.NativeRetract,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DependencyPieces,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SubsetCoproduct,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.StrictComparison,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PresentationReduction,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SemifreeLabels,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.GradedSphereSupport,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.GradedExtension,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SmallSemifree,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SubsetModule,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ConeEmbedding,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionLabels,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionSupport,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionDependencies,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.CellAttachment,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialStage,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.FilteredUnion,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.FilteredEmbedding,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.SequencePrepend,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialTower,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialSemifree,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialStageMaps,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialEmbedding,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.PartialMaps,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionCovering,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionDiagram,
    `SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.Covers]
  let mut count := 0
  let mut seen : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if info.isAxiom then throwError "New axiom: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    if (info.type.find? fun e => match e with
      | .const n _ => n.getString! == "ModelCategory"
      | _ => false).isSome then
      throwError "ModelCategory assumption in {name}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D-e axiom/signature audit passed: {count} declarations in {seen.size} modules."

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectComparison
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectComparison_isQCatEquivalence
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectComparison_inclusionIso
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput

#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCompact_retract_of_nativeCellPresentation
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaClosedProjectiveObjects_nativeRetractCovers
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaDependencyPieces_nerve_isKappaFiltered
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetCoproductIsColimit
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictFilteredColimitComparison
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCovers_of_strictRepresentativePresentation
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaClosedProjectiveObjects_smallSemifreeCovers
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaSubsetModule_finiteElement
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaModuleConeMap_degreewiseMono
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionStrictRepresentativePresentation
#check SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCone_covers_of_strictFilteredColimitComparison
