import SerrePositivity.Spectra.ModelCategory.GeneralLevelEnriched
import SerrePositivity.Spectra.ModelCategory.LeftProper
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel
open SerrePositivity.Quillen

-- Start with an arbitrary monoidal model source. The actual spectral model,
-- pushout-product, unit and chosen C-valued enrichment are all outputs.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
    (K : C) [IsCofibrant K] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J] :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      let := m
      MonoidalModelCategory (GeneralSymmetricSpectrum C K) ∧
      (letI : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
        mappingEnrichedOrdinaryCategory
      IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor ∧
      HasQuillenPullbackHom (eHomFunctor C (GeneralSymmetricSpectrum C K)) ∧
      HasQuillenPullbackHom (spectrumTensorCotensor (K := K)).cotensor ∧
      Enriched.HasTensorUnitAxiom (spectrumTensorCotensor (K := K))) := by
  obtain ⟨m, hW, hF, hC, hgen, hproper⟩ := exists_leftProper_levelModel_of_monoidal K I J
  let := m
  have : CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := hgen
  have : ∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n) := fun n ↦
    freeAt_isLeftQuillen_of_level_classes K hW hF n
  let : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
    mappingEnrichedOrdinaryCategory
  have h := general_levelEnriched_model K I J
  exact ⟨m, general_levelTensor_monoidalModel K I J, h.1, h.2.1, h.2.2,
    general_levelEnriched_unit K⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.Spectra.General.TensorFreeAtSum,
    `SerrePositivity.Spectra.General.FreePushoutProduct,
    `SerrePositivity.Spectra.ModelCategory.GeneralLevelTensor,
    `SerrePositivity.Spectra.ModelCategory.GeneralLevelEnriched]
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
  unless modules.size == expected.size do throwError "Some general level monoidal modules were not audited"
  logInfo m!"General level monoidal audit passed: {count} declarations in {modules.size} modules, standard axioms only."
