module

public import SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor
public import SerrePositivity.Spectra.General.EnrichedModel
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorCotensor

/-! # The pointed simplicial action and mapping SM7 on the actual level model -/

@[expose] public section
universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.SimplicialModelInputs
open SerrePositivity.Quillen

abbrev pointedSpectrumTensor : PointedSimplicialSet.{u} ⥤
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  GeneralSymmetricSpectrum.pointwiseTensorBifunctor (K := PointedSimplicialSet.circle.{u})

abbrev pointedSpectrumCotensor : PointedSimplicialSet.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  GeneralSymmetricSpectrum.cotensorBifunctor (K := PointedSimplicialSet.circle.{u})

abbrev pointedSpectrumMapping : SymmetricSpectrum.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ PointedSimplicialSet.{u} :=
  GeneralSymmetricSpectrum.mappingObjectBifunctor (K := PointedSimplicialSet.circle.{u})

abbrev ordinarySpectrumTensor : SSet.{u} ⥤ SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  PointedObject.adjoinFunctor ⋙ pointedSpectrumTensor

abbrev ordinarySpectrumCotensor : SSet.{u}ᵒᵖ ⥤ SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  PointedObject.adjoinFunctor.op ⋙ pointedSpectrumCotensor

lemma ordinarySpectrumTensor_obj (K : SSet.{u}) :
    ordinarySpectrumTensor.obj K = SymmetricSpectrum.simplicialTensorFunctor K := rfl

lemma ordinarySpectrumCotensor_obj (K : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    (ordinarySpectrumCotensor.obj (Opposite.op K)).obj E =
      SymmetricSpectrum.simplicialCotensor K E :=
  GeneralSymmetricSpectrum.simplicial_cotensor (PointedObject.adjoin K) E

variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

lemma pointedSpectrumTensor_isQuillen :
    let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor pointedSpectrumTensor.{u} := by
  let : ModelCategory SymmetricSpectrum.{u} := simplicialLevelModelCategory hCof hFib
  let : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u}
      PointedSimplicialSet.circle) := simplicialLevelModelCategory hCof hFib
  let : IsLeftQuillen (GeneralSymmetricSpectrum.freeAt (K := PointedSimplicialSet.circle.{u}) 0) :=
    simplicialLevel_freeAt_isLeftQuillen hCof hFib 0
  let : IsQuillenBifunctor (CategoryTheory.MonoidalCategory.curriedTensor
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} PointedSimplicialSet.circle)) :=
    simplicialLevelTensor_isQuillen hCof hFib
  exact GeneralSymmetricSpectrum.pointwiseTensor_isQuillen

lemma pointedSpectrumCotensor_SM7 :
    let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom pointedSpectrumCotensor.{u} := by
  let : ModelCategory SymmetricSpectrum.{u} := simplicialLevelModelCategory hCof hFib
  let : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u}
      PointedSimplicialSet.circle) := simplicialLevelModelCategory hCof hFib
  exact (isQuillenBifunctor_iff_pullbackHom
    (GeneralSymmetricSpectrum.pointwiseTensorCotensorParametrizedAdjunction
      (K := PointedSimplicialSet.circle.{u}))).1 (pointedSpectrumTensor_isQuillen hCof hFib)

lemma pointedSpectrumMapping_SM7 :
    let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom pointedSpectrumMapping.{u} := by
  let : ModelCategory SymmetricSpectrum.{u} := simplicialLevelModelCategory hCof hFib
  let : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u}
      PointedSimplicialSet.circle) := simplicialLevelModelCategory hCof hFib
  let : IsQuillenBifunctor
      (GeneralSymmetricSpectrum.pointwiseTensorBifunctor (K := PointedSimplicialSet.circle.{u})) :=
    pointedSpectrumTensor_isQuillen hCof hFib
  exact (isQuillenBifunctor_iff_pullbackHom
    (GeneralSymmetricSpectrum.pointwiseTensorMappingParametrizedAdjunction
      (K := PointedSimplicialSet.circle.{u}))).1 inferInstance

lemma ordinarySpectrumTensor_isQuillen :
    let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor ordinarySpectrumTensor.{u} := by
  let := simplicialLevelModelCategory hCof hFib
  let : IsQuillenBifunctor pointedSpectrumTensor.{u} := pointedSpectrumTensor_isQuillen hCof hFib
  let : IsLeftQuillen (PointedObject.adjoinFunctor : SSet.{u} ⥤ PointedSimplicialSet.{u}) :=
    SerrePositivity.PointedModel.adjoin_isLeftQuillen
  exact isQuillenBifunctor_restrict _

lemma ordinarySpectrumCotensor_SM7 :
    let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom ordinarySpectrumCotensor.{u} := by
  let : ModelCategory SymmetricSpectrum.{u} := simplicialLevelModelCategory hCof hFib
  let : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u}
      PointedSimplicialSet.circle) := simplicialLevelModelCategory hCof hFib
  exact (isQuillenBifunctor_iff_pullbackHom
    (SerrePositivity.ParametrizedAdjunctionTransport.restrict
      (GeneralSymmetricSpectrum.pointwiseTensorCotensorParametrizedAdjunction
        (K := PointedSimplicialSet.circle.{u})) PointedObject.adjoinFunctor)).1
    (ordinarySpectrumTensor_isQuillen hCof hFib)

end SerrePositivity.SimplicialModelInputs
