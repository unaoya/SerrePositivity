import SerrePositivity.Spectra.Stable.EnrichedModel
import SerrePositivity.Spectra.ModelCategory.LeftProper
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.ModelGeneration SerrePositivity.SpectrumLevelModel
open SerrePositivity.SpectrumStabilization SerrePositivity.Quillen

-- Final S2 consumer. Construct the original and localized models, then derive
-- all localized tensor, enriched Hom and cotensor conditions. Tensor
-- compatibility and Omega preservation are not extra inputs.
example {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
    [ModelCategory C] [IsLocallyPresentable.{w} C]
    [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]
    [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant (𝟙_ C)]
    (K : C) [IsCofibrant K] (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
    (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)
    [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
    (IS JS : MorphismProperty SSet.{w}) [CofibrantlyGenerated.{w} IS JS]
    (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
    (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
    (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences) :
    ∃ m : ModelCategory (GeneralSymmetricSpectrum C K),
      let := m
      ∃ (cofSp : MorphismProperty.FunctorialFactorizationData
          (cofibrations (GeneralSymmetricSpectrum C K))
          (trivialFibrations (GeneralSymmetricSpectrum C K)))
        (fibSp : MorphismProperty.FunctorialFactorizationData
          (trivialCofibrations (GeneralSymmetricSpectrum C K))
          (fibrations (GeneralSymmetricSpectrum C K)))
        (p : StableModelPresentation.{w} K cofSp fibSp (levelGenerators K I)),
        let := p.localization.model
        letI : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
          mappingEnrichedOrdinaryCategory
        MonoidalModelCategory (GeneralSymmetricSpectrum C K) ∧
          IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor ∧
          HasQuillenPullbackHom (eHomFunctor C (GeneralSymmetricSpectrum C K)) ∧
          HasQuillenPullbackHom (spectrumTensorCotensor (K := K)).cotensor ∧
          Enriched.HasTensorUnitAxiom (spectrumTensorCotensor (K := K)) := by
  obtain ⟨m, hW, hF, hC, hgen, hproper⟩ := exists_leftProper_levelModel_of_monoidal K I J
  let := m
  have : CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J) := hgen
  have : (weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
      (cofibrations (GeneralSymmetricSpectrum C K)) := hproper
  have := hasFunctorialFactorization_cofibration_trivialFibration
    (levelGenerators K I) (levelGenerators K J)
  have := hasFunctorialFactorization_trivialCofibration_fibration
    (levelGenerators K I) (levelGenerators K J)
  let cofSp := MorphismProperty.functorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K))
  let fibSp := MorphismProperty.functorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K))
  obtain ⟨p⟩ := exists_stableModelPresentation K cofSp fibSp (levelGenerators K I)
    I J (levelGenerators K J) hW hF IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  have : ∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n) := fun n ↦
    freeAt_isLeftQuillen_of_level_classes K hW hF n
  let : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
    mappingEnrichedOrdinaryCategory
  have hM := p.monoidal_model (K := K) (I := I) (J := J) (cofSp := cofSp) (fibSp := fibSp)
    (hcof := hcofV) (hfib := hfibV) (hdom := hdom)
  have hE := p.enriched_model (K := K) (I := I) (J := J) (cofSp := cofSp) (fibSp := fibSp)
    (hcof := hcofV) (hfib := hfibV) (hdom := hdom)
  have hU := p.enriched_unit (K := K) (I := I) (cofSp := cofSp) (fibSp := fibSp) (hcof := hcofV)
  exact ⟨m, cofSp, fibSp, p, hM, hE.1, hE.2.1, hE.2.2, hU⟩

section SeparateUnit
-- Keep the original unit axioms as data; no cofibrancy of either unit is assumed.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [base : ModelCategory C] [IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)]
  [ModelCategory SSet.{v}]
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (p : StableModelPresentation.{w} K cofSp fibSp (levelGenerators K I))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)

example (hu : HasUnitAxiom (GeneralSymmetricSpectrum C K)) :
    @MonoidalModelCategory (GeneralSymmetricSpectrum C K) _ p.localization.model _ :=
  p.monoidal_model_of_original_unit K I J cofSp fibSp hcof hfib hdom hu

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

example (hu : Enriched.HasTensorUnitAxiom (spectrumTensorCotensor (K := K))) :
    @Enriched.HasTensorUnitAxiom C _ _ base (GeneralSymmetricSpectrum C K) _
      p.localization.model _ (spectrumTensorCotensor (K := K)) :=
  p.enriched_unit_of_original K I cofSp fibSp hcof hu
end SeparateUnit

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.Endofunctor,
    `SerrePositivity.Spectra.Stable.TensorCompatibility,
    `SerrePositivity.Spectra.Stable.EnrichedModel]
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
  unless modules.size == expected.size do throwError "Some stable enriched modules were not audited"
  logInfo m!"Stable enriched audit passed: {count} declarations in {modules.size} modules, standard axioms only."
