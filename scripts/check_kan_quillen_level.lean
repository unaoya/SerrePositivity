import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.SimplicialLevel
import SerrePositivity.Spectra.StageTwo
import Lean.Util.CollectAxioms
import Lean.Util.Sorry

universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.Inputs.Homotopy
open SerrePositivity.SimplicialModelInputs SerrePositivity.Quillen

-- Actual local selections: no ModelCategory SSet input is assumed here.
local instance : ModelCategory SSet.{u} := kanQuillenModel

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ geometricWeakEquivalences f := by
  rw [weakEquivalence_iff, kanQuillenModel_weakEquivalences]
example : MonoidalModelCategory PointedSimplicialSet.{u} :=
  pointedSimplicial_monoidalModel kanQuillenModel_cofibrations kanQuillenModel_fibrations
example : HasQuillenPullbackHom
    (MonoidalClosed.internalHom (C := PointedSimplicialSet.{u})) :=
  pointedSimplicial_SM7 kanQuillenModel_cofibrations kanQuillenModel_fibrations
example : ModelCategory SymmetricSpectrum.{u} := circleSpectrumLevelModel
example : let := circleSpectrumLevelModel.{u}
    MonoidalModelCategory SymmetricSpectrum.{u} := circleSpectrumLevelModel_monoidal
example : let := circleSpectrumLevelModel.{u}
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SymmetricSpectrum.{u})) :=
  circleSpectrumLevelModel_SM7
example : let := circleSpectrumLevelModel.{u}
    HasQuillenPullbackHom pointedSpectrumMapping.{u} := circleSpectrumLevelModel_pointedMapping_SM7
example : let := circleSpectrumLevelModel.{u}
    IsQuillenBifunctor ordinarySpectrumTensor.{u} := circleSpectrumLevelModel_simplicialTensor_isQuillen
example : let := circleSpectrumLevelModel.{u}
    HasQuillenPullbackHom ordinarySpectrumCotensor.{u} := circleSpectrumLevelModel_simplicialCotensor_SM7
example : let := circleSpectrumLevelModel.{u}
    HasQuillenPullbackHom ordinarySpectrumMapping.{u} := circleSpectrumLevelModel_simplicialMapping_SM7
example : let := circleSpectrumLevelModel.{u}
    let : EnrichedOrdinaryCategory SSet.{u} SymmetricSpectrum.{u} :=
      SymmetricSpectrum.mappingSpaceSimplicialCategory
    HasQuillenPullbackHom (eHomFunctor SSet.{u} SymmetricSpectrum.{u}) :=
  circleSpectrumLevelModel_enrichedHom_SM7
example : let := circleSpectrumLevelModel.{u}
    ModelGeneration.CofibrantlyGenerated.{u} simplicialLevelI.{u} simplicialLevelJ.{u} :=
  circleSpectrumLevelModel_generated
example (n : ℕ) : let := circleSpectrumLevelModel.{u}
    IsRightQuillen (SymmetricSpectrum.evaluation.{u} n) :=
  simplicialLevel_evaluation_isRightQuillen
    kanQuillenModel_cofibrations kanQuillenModel_fibrations n
example (n : ℕ) : let := circleSpectrumLevelModel.{u}
    IsLeftQuillen (SymmetricSpectrum.freeAt.{u} n) :=
  simplicialLevel_freeAt_isLeftQuillen
    kanQuillenModel_cofibrations kanQuillenModel_fibrations n
example : let := circleSpectrumLevelModel.{u}
    (cofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (trivialFibrations SymmetricSpectrum.{u}) ∧
      (trivialCofibrations SymmetricSpectrum.{u}).HasFunctorialFactorization
        (fibrations SymmetricSpectrum.{u}) :=
  simplicialLevel_functorialFactorizations kanQuillenModel_cofibrations kanQuillenModel_fibrations

open Lean in
run_cmd do
  let env ← getEnv
  let mut directInputs : Array Name := #[]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless #[`SerrePositivity.InfinityCategories.ModelBridge.Inputs.KanQuillen,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.SimplicialLevel,
        `SerrePositivity.Spectra.ModelCategory.SimplicialWeakEquivalences,
        `SerrePositivity.HomotopicalAlgebra.Topological.WeakEquivalence].contains mod do continue
    if (info.value? true).any (·.hasSorry) then directInputs := directInputs.push name
    let axioms ← collectAxioms name
    let allowed := if #[`SerrePositivity.InfinityCategories.ModelBridge.Inputs.KanQuillen,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.ResolutionHom,
        `SerrePositivity.InfinityCategories.ModelBridge.Inputs.SimplicialLevel].contains mod then
        #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
      else #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  unless directInputs == #[``kanQuillen_model_exists] do
    throwError "Expected exactly HT-KQ as the direct literature input, got {directInputs}"
  logInfo m!"Kan–Quillen level audit passed: {count} declarations; sole direct citation HT-KQ."
