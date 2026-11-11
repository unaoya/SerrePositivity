module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.KanQuillen
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevel
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevelEnriched
public import SerrePositivity.Spectra.ModelCategory.SimplicialHomComparison

/-! # Applying HT-KQ to the proved simplicial level construction

This upper entry uses the single model-existence citation in `KanQuillen`.
The lower construction remains independent of all literature inputs.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs
open SimplicialModelInputs

/-- The actual circle-based simplicial spectrum level model using HT-KQ. -/
@[instance_reducible]
def circleSpectrumLevelModel : ModelCategory SymmetricSpectrum.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact simplicialLevelModelCategory _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_generated :
    let := circleSpectrumLevelModel.{u}
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} simplicialLevelI.{u} simplicialLevelJ.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact simplicialLevelModelCategory_generated
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_monoidal :
    let := circleSpectrumLevelModel.{u}
    Quillen.MonoidalModelCategory SymmetricSpectrum.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact simplicialLevelTensor_monoidalModel
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_SM7 :
    let := circleSpectrumLevelModel.{u}
    Quillen.HasQuillenPullbackHom
      (MonoidalClosed.internalHom (C := SymmetricSpectrum.{u})) := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact simplicialLevelTensor_SM7 _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_pointedMapping_SM7 :
    let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
    let := circleSpectrumLevelModel.{u}
    Quillen.HasQuillenPullbackHom pointedSpectrumMapping.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact pointedSpectrumMapping_SM7 _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_simplicialTensor_isQuillen :
    let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
    let := circleSpectrumLevelModel.{u}
    Quillen.IsQuillenBifunctor ordinarySpectrumTensor.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact ordinarySpectrumTensor_isQuillen _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_simplicialCotensor_SM7 :
    let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
    let := circleSpectrumLevelModel.{u}
    Quillen.HasQuillenPullbackHom ordinarySpectrumCotensor.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact ordinarySpectrumCotensor_SM7 _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_simplicialMapping_SM7 :
    let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
    let := circleSpectrumLevelModel.{u}
    Quillen.HasQuillenPullbackHom ordinarySpectrumMapping.{u} := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact ordinarySpectrumMapping_SM7 _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_enrichedHom_SM7 :
    let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
    let := circleSpectrumLevelModel.{u}
    let : EnrichedOrdinaryCategory SSet.{u} SymmetricSpectrum.{u} :=
      SymmetricSpectrum.mappingSpaceSimplicialCategory
    Quillen.HasQuillenPullbackHom (eHomFunctor SSet.{u} SymmetricSpectrum.{u}) := by
  let : ModelCategory SSet.{u} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel
  exact legacyOrdinaryHom_SM7 _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_cofibrations _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs.kanQuillenModel_fibrations

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Inputs
