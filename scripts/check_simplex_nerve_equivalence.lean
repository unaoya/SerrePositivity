import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

-- General cell detection, independent of the specific simplex-nerve functor.
example {U V : SSet.{max u v} ⥤ SSet.{max u v}} (η : U ⟶ V)
    [PreservesColimitsOfSize.{max u v, max u v} U]
    [PreservesColimitsOfSize.{max u v, max u v} V]
    [U.PreservesMonomorphisms] [V.PreservesMonomorphisms]
    (hstd : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map
      (η.app (SSet.stdSimplex.obj (SimplexCategory.mk n))))) (X : SSet.{max u v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (η.app X)) :=
  CellularNaturalComparison.app_isIso η hstd X

-- Every actual X is allowed, without a dimension bound, a Kan condition, or a value model.
example (X : SSet.{max u v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SimplexNerve.augmentation.app X)) :=
  SimplexNerve.augmentation_localized_isIso X

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : SimplexNerve.functor ⋙ L ≅ L :=
  SimplexNerve.augmentationImageIso L hL

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) (X : SSet.{max u v}) :
    ((SimplexNerve.augmentationImageIso L hL).app X).hom =
      L.map (SimplexNerve.augmentation.app X) :=
  SimplexNerve.augmentationImageIso_hom L hL X

-- The two exact pre-existing bar augmentations, including both explicit lift wrappers.
open SerrePositivity.HomotopyFunctionComplex in
example {C : Type u} [Category.{v} C] [ModelCategory C] (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarNerveBridge.simplexAugmentation R)) :=
  OrdinaryBarAugmentationEquivalences.large_localized_isIso R

open SerrePositivity.HomotopyFunctionComplex in
example {C : Type u} [Category.{v} C] [ModelCategory C] (R : RightResolutionMapping.Index C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluatedEndpoint.smallAugmentation R)) :=
  OrdinaryBarAugmentationEquivalences.small_localized_isIso R

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SkeletalDimension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CellularNaturalComparison,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarAugmentationEquivalences]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do throwError "Missing Simplex nerve equivalence modules"
  logInfo m!"Simplex nerve equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
