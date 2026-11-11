module

public import SerrePositivity.Spectra.Stable.TensorCompatibility
public import SerrePositivity.Spectra.ModelCategory.GeneralLevelEnriched
public import SerrePositivity.HomotopicalAlgebra.Localization.Enriched
public import SerrePositivity.HomotopicalAlgebra.Localization.Monoidal
public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitChangeModel

/-! # Monoidal and enriched model conditions after actual spectral localization

The tensor compatibility is proved from Omega preservation, not assumed.
Cofibrant domains of the base generating cofibrations are explicit additional
conditions for this enriched/monoidal result. They do not enter the ordinary
localization existence theorem.
-/

@[expose] public section
universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum
open SerrePositivity.Quillen SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [base : ModelCategory C] [IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [levelModel : ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (SpectrumLevelModel.levelGenerators K I)
    (SpectrumLevelModel.levelGenerators K J)]
  [ModelCategory SSet.{v}]
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (p : StableModelPresentation.{w} K cofSp fibSp (SpectrumLevelModel.levelGenerators K I))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hdom : ∀ {A B : C} (i : A ⟶ B), I i → IsCofibrant A)

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

include I J hcof hfib hdom in
lemma StableModelPresentation.enriched_model :
    @IsQuillenBifunctor C _ base (GeneralSymmetricSpectrum C K) _ p.localization.model
      (GeneralSymmetricSpectrum C K) _ p.localization.model
        (spectrumTensorCotensor (K := K)).tensor ∧
    @HasQuillenPullbackHom (GeneralSymmetricSpectrum C K) _ p.localization.model C _ base
      (GeneralSymmetricSpectrum C K) _ p.localization.model
        (eHomFunctor C (GeneralSymmetricSpectrum C K)) ∧
    @HasQuillenPullbackHom C _ base (GeneralSymmetricSpectrum C K) _ p.localization.model
      (GeneralSymmetricSpectrum C K) _ p.localization.model
        (spectrumTensorCotensor (K := K)).cotensor := by
  have := SpectrumLevelModel.general_levelTensor_isQuillen K I J
  have hP : IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor :=
    pointwiseTensor_isQuillen
  have hg : @_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (GeneralSymmetricSpectrum C K) _ p.localization.model
      (SpectrumLevelModel.levelGenerators K I) p.localization.generators := p.localization.generated
  apply p.isLocalizationModel.enriched_model_of_tensor_compatible (V := C) hcof hfib
    (spectrumTensorCotensor (K := K)) hP I J
    (SpectrumLevelModel.levelGenerators K I) p.localization.generators hdom
  intro A B i hi X Y s hs
  have : IsCofibrant A := hdom i hi
  have : Cofibration i :=
    ⟨(I.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J).symm.le) i hi⟩
  have : IsCofibrant B := isCofibrant_of_cofibration i
  exact ⟨p.pointwiseTensor_compatible K cofSp fibSp _ hcof hfib A s hs,
    p.pointwiseTensor_compatible K cofSp fibSp _ hcof hfib B s hs⟩

include I J hcof hfib hdom in
lemma StableModelPresentation.monoidal_model_of_original_unit
    (hu : HasUnitAxiom (GeneralSymmetricSpectrum C K)) :
    @MonoidalModelCategory (GeneralSymmetricSpectrum C K) _ p.localization.model _ := by
  have hF := SpectrumLevelModel.general_levelTensor_isQuillen K I J
  have : IsQuillenBifunctor (curriedTensor (GeneralSymmetricSpectrum C K)) := hF
  have hg : @_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (GeneralSymmetricSpectrum C K) _ p.localization.model
      (SpectrumLevelModel.levelGenerators K I) p.localization.generators := p.localization.generated
  apply p.isLocalizationModel.monoidal_model_of_tensor_compatible hcof hfib
    (SpectrumLevelModel.levelGenerators K I) (SpectrumLevelModel.levelGenerators K J)
    p.localization.generators hF hu
  · change ∀ {A B : GeneralSymmetricSpectrum C K} (i : A ⟶ B),
      SpectrumLevelModel.levelGenerators K I i → IsCofibrant A
    intro A B i hi
    change (⨆ n : ℕ, I.strictMap (freeAt (K := K) n)) i at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, hi⟩ := hi
    cases hi with
    | map hi =>
      have := (freeAtAdjunction (K := K) n).isLeftAdjoint
      have := hdom _ hi
      exact map_isCofibrant (freeAt (K := K) n) _
  · intro A B i hi X Y s hs
    change (⨆ n : ℕ, I.strictMap (freeAt (K := K) n)) i at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, hi⟩ := hi
    cases hi with
    | @map A' B' i' hi =>
      have : IsCofibrant A' := hdom i' hi
      have : Cofibration i' :=
        ⟨(I.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J).symm.le) i' hi⟩
      have : IsCofibrant B' := isCofibrant_of_cofibration i'
      exact ⟨p.freeTensor_compatible K cofSp fibSp _ hcof hfib n A' s hs,
        p.freeTensor_compatible K cofSp fibSp _ hcof hfib n B' s hs⟩

include I J hcof hfib hdom in
lemma StableModelPresentation.monoidal_model [IsCofibrant (𝟙_ C)] :
    @MonoidalModelCategory (GeneralSymmetricSpectrum C K) _ p.localization.model _ :=
  p.monoidal_model_of_original_unit K I J cofSp fibSp hcof hfib hdom
    (SpectrumLevelModel.general_levelTensor_monoidalModel K I J).unit

omit [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)] in
include hcof in
lemma StableModelPresentation.enriched_unit_of_original
    (hu : Enriched.HasTensorUnitAxiom (spectrumTensorCotensor (K := K))) :
    @Enriched.HasTensorUnitAxiom C _ _ base (GeneralSymmetricSpectrum C K) _
      p.localization.model _ (spectrumTensorCotensor (K := K)) := by
  have hw : weakEquivalences (GeneralSymmetricSpectrum C K) ≤
      p.localization.model.categoryWithWeakEquivalences.weakEquivalences :=
    (Bousfield.weakEquivalences_le_localEquivalences cofSp fibSp hcof
      (localizingMaps K p.tests)).trans p.localization.weakEquivalences_eq.symm.le
  exact Enriched.hasTensorUnitAxiom_change_model levelModel p.localization.model
    (spectrumTensorCotensor (K := K)) p.localization.cofibrations_eq hw hu

omit [IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)] in
include hcof in
lemma StableModelPresentation.enriched_unit [IsCofibrant (𝟙_ C)] :
    @Enriched.HasTensorUnitAxiom C _ _ base (GeneralSymmetricSpectrum C K) _
      p.localization.model _ (spectrumTensorCotensor (K := K)) :=
  p.enriched_unit_of_original K I cofSp fibSp hcof
    (Enriched.tensorUnitAxiom_of_cofibrant_unit _)

end SerrePositivity.SpectrumStabilization
