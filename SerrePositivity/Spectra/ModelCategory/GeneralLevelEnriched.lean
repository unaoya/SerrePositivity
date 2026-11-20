module

public import SerrePositivity.Spectra.ModelCategory.GeneralLevelTensor
public import SerrePositivity.Spectra.General.EnrichedModel
public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitAxiom

/-! # The actual C-enrichment on a general spectrum level model

The proved level pushout-product axiom and free-zero adjunction supply the
model condition on the existing pointwise tensor, cotensor and enriched Hom.
Only the separate action-unit conclusion assumes a cofibrant unit in C.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.Quillen

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [IsQuillenBifunctor (curriedTensor C)] (K : C)
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)]

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

include I J in
lemma general_levelEnriched_model :
    IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor ∧
      HasQuillenPullbackHom (eHomFunctor C (GeneralSymmetricSpectrum C K)) ∧
      HasQuillenPullbackHom (spectrumTensorCotensor (K := K)).cotensor := by
  have := general_levelTensor_isQuillen K I J
  exact ⟨pointwiseTensor_isQuillen,
    (Enriched.tensor_iff_mapping_model (spectrumTensorCotensor (K := K))).1
      pointwiseTensor_isQuillen,
    (isQuillenBifunctor_iff_pullbackHom pointwiseTensorCotensorParametrizedAdjunction).1
      pointwiseTensor_isQuillen⟩

omit [IsQuillenBifunctor (curriedTensor C)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)] in
lemma general_levelEnriched_unit [IsCofibrant (𝟙_ C)] :
    Enriched.HasTensorUnitAxiom (spectrumTensorCotensor (K := K)) :=
  Enriched.tensorUnitAxiom_of_cofibrant_unit _

end SerrePositivity.SpectrumLevelModel
