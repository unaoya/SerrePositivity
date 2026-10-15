module

public import SerrePositivity.Spectra.Stable.ModelCategory
public import SerrePositivity.Spectra.Stable.InternalHomOmega
public import SerrePositivity.Spectra.General.EnrichedModel
public import SerrePositivity.HomotopicalAlgebra.Localization.Endofunctor

/-! # Actual tensor compatibility for the constructed spectral localization

Cotensor and internal Hom from a free cofibrant coefficient preserve the
independently defined Omega condition. The general Quillen universal property
therefore extends their left adjoints to the localized model. Its derived
generator criterion then supplies the actual local-equivalence tensor tests.
-/

@[expose] public section
universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [levelModel : ModelCategory (GeneralSymmetricSpectrum C K)]
  [Quillen.IsQuillenBifunctor (curriedTensor (GeneralSymmetricSpectrum C K))]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)]
  [simplicial : ModelCategory SSet.{v}]
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (IP : MorphismProperty (GeneralSymmetricSpectrum C K))
  (p : StableModelPresentation.{w} K cofSp fibSp IP)
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

include hcof hfib in
lemma StableModelPresentation.pointwiseTensor_isLeftQuillen (X : C) [IsCofibrant X] :
    @Quillen.IsLeftQuillen (GeneralSymmetricSpectrum C K) _ (GeneralSymmetricSpectrum C K) _
      p.localization.model.categoryWithCofibrations
      p.localization.model.categoryWithWeakEquivalences
      p.localization.model.categoryWithCofibrations
      p.localization.model.categoryWithWeakEquivalences
      (pointwiseTensorFunctor X) := by
  have : Quillen.IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor :=
    pointwiseTensor_isQuillen
  have hF : Quillen.IsLeftQuillen (pointwiseTensorFunctor (K := K) X) :=
    Enriched.tensor_isLeftQuillen (spectrumTensorCotensor (K := K)) X
  apply p.isLocalizationModel.endofunctor_isLeftQuillen_of_rightAdjoint_local hcof hfib
    (pointwiseTensorCotensorAdjunction X) hF
  intro Y hY
  have hR : p.localization.model.categoryWithFibrations.fibrations
      (terminal.from ((cotensorFunctor (K := K) X).obj Y)) := by
    apply (p.fibrant_iff _).mpr
    exact cotensor_isFibrantOmega X Y ((p.fibrant_iff Y).mp hY)
  exact ((p.isLocalizationModel.fibrant_iff _).mp hR).2

include hcof hfib in
lemma StableModelPresentation.freeTensor_isLeftQuillen (n : ℕ) (X : C) [IsCofibrant X] :
    @Quillen.IsLeftQuillen (GeneralSymmetricSpectrum C K) _ (GeneralSymmetricSpectrum C K) _
      p.localization.model.categoryWithCofibrations
      p.localization.model.categoryWithWeakEquivalences
      p.localization.model.categoryWithCofibrations
      p.localization.model.categoryWithWeakEquivalences
      (tensorLeft ((freeAt (K := K) n).obj X)) := by
  have := (freeAtAdjunction (K := K) n).isLeftAdjoint
  have := Quillen.map_isCofibrant (freeAt (K := K) n) X
  have hF := Quillen.tensorLeft_isLeftQuillen ((freeAt (K := K) n).obj X)
  apply p.isLocalizationModel.endofunctor_isLeftQuillen_of_rightAdjoint_local hcof hfib
    (ihom.adjunction ((freeAt (K := K) n).obj X)) hF
  intro Y hY
  have hR : p.localization.model.categoryWithFibrations.fibrations
      (terminal.from ((ihom ((freeAt (K := K) n).obj X)).obj Y)) := by
    apply (p.fibrant_iff _).mpr
    exact internalHomFreeAt_isFibrantOmega n X Y ((p.fibrant_iff Y).mp hY)
  exact ((p.isLocalizationModel.fibrant_iff _).mp hR).2

include hcof hfib in
lemma StableModelPresentation.pointwiseTensor_compatible (X : C) [IsCofibrant X]
    {E F : GeneralSymmetricSpectrum C K} (s : E ⟶ F) (hs : localizingMaps K p.tests s) :
    Bousfield.localEquivalences cofSp fibSp (localizingMaps K p.tests)
      ((pointwiseTensorFunctor X).map ((cofibrantSource cofSp).map s)) := by
  have : Quillen.IsQuillenBifunctor (spectrumTensorCotensor (K := K)).tensor :=
    pointwiseTensor_isQuillen
  have hF : Quillen.IsLeftQuillen (pointwiseTensorFunctor (K := K) X) :=
    Enriched.tensor_isLeftQuillen (spectrumTensorCotensor (K := K)) X
  exact (p.isLocalizationModel.endofunctor_isLeftQuillen_iff hcof hfib
    (pointwiseTensorCotensorAdjunction X) hF).mp
      (p.pointwiseTensor_isLeftQuillen K cofSp fibSp IP hcof hfib X) s hs

include hcof hfib in
lemma StableModelPresentation.freeTensor_compatible (n : ℕ) (X : C) [IsCofibrant X]
    {E F : GeneralSymmetricSpectrum C K} (s : E ⟶ F) (hs : localizingMaps K p.tests s) :
    Bousfield.localEquivalences cofSp fibSp (localizingMaps K p.tests)
      ((tensorLeft ((freeAt (K := K) n).obj X)).map ((cofibrantSource cofSp).map s)) := by
  have := (freeAtAdjunction (K := K) n).isLeftAdjoint
  have := Quillen.map_isCofibrant (freeAt (K := K) n) X
  have hF := Quillen.tensorLeft_isLeftQuillen ((freeAt (K := K) n).obj X)
  exact (p.isLocalizationModel.endofunctor_isLeftQuillen_iff hcof hfib
    (ihom.adjunction ((freeAt (K := K) n).obj X)) hF).mp
      (p.freeTensor_isLeftQuillen K cofSp fibSp IP hcof hfib n X) s hs

end SerrePositivity.SpectrumStabilization
