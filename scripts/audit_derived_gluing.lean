import SerrePositivity.InfinityCategories.Derived.Gluing
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.InfinityCategories.Derived.Gluing.Objects,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ActionElements,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomComplex,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomCalculus,
    `SerrePositivity.InfinityCategories.Derived.Gluing.RepresentableModel,
    `SerrePositivity.InfinityCategories.Derived.Gluing.AugmentationElements,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ActionYoneda,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomComparison,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomComparisonProjections,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomTransport,
    `SerrePositivity.InfinityCategories.Derived.Gluing.Category,
    `SerrePositivity.InfinityCategories.Derived.Gluing.Projections,
    `SerrePositivity.InfinityCategories.Derived.Gluing.Composition,
    `SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CompositionComparison,
    `SerrePositivity.InfinityCategories.Derived.Gluing.Postcomposition,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ClosedSquareHomotopy,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeSquare,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CoconeSquare,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeCoconeComparison,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeCoconeIso,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CoconeExtraction,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeComparison,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ClosedCompositionCochain,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostcomposition,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostBottom,
    `SerrePositivity.InfinityCategories.Derived.Gluing.InclusionTransport,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeBottomAction,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ModulePostAction,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostHomotopy,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeHomotopyAction,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeExplicit,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeBiproduct,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeSquareRestriction,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeSplit,
    `SerrePositivity.InfinityCategories.Derived.Gluing.HomConeBlocks,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeCoefficient,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeModule,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ModuleConeSquareIso,
    `SerrePositivity.InfinityCategories.Derived.Gluing.KernelCone,
    `SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelCone,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeRepresentative,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeObject,
    `SerrePositivity.InfinityCategories.Derived.Gluing.ConeObjectTransport]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"D2 gluing axiom audit passed: {count} declarations in {seen.size} modules."
