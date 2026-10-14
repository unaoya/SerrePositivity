module

public import SerrePositivity.Spectra.General.TensorCotensorEnriched
public import SerrePositivity.HomotopicalAlgebra.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.Monoidal.BifunctorTransport

/-! # Model compatibility of the existing spectrum enrichment

The enriching category is arbitrary. A left Quillen free-zero functor and
the spectrum pushout-product condition imply the actual action/cotensor and
mapping-object SM7 conditions, through the existing natural comparison.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra SerrePositivity.Quillen
namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}
  [ModelCategory C] [ModelCategory (GeneralSymmetricSpectrum C K)]
  [IsLeftQuillen (freeAt (K := K) 0)]
  [IsQuillenBifunctor (curriedTensor (GeneralSymmetricSpectrum C K))]

lemma pointwiseTensor_isQuillen : IsQuillenBifunctor (pointwiseTensorBifunctor (K := K)) := by
  let : IsQuillenBifunctor ((freeAt (K := K) 0) ⋙
      curriedTensor (GeneralSymmetricSpectrum C K)) := isQuillenBifunctor_restrict _
  exact isQuillenBifunctor_of_natIso tensorFreeZeroPointwiseBifunctorIso

lemma cotensor_hasQuillenPullbackHom : HasQuillenPullbackHom (cotensorBifunctor (K := K)) :=
  (isQuillenBifunctor_iff_pullbackHom pointwiseTensorCotensorParametrizedAdjunction).1
    pointwiseTensor_isQuillen

lemma mappingObject_hasQuillenPullbackHom :
    HasQuillenPullbackHom (mappingObjectBifunctor (K := K)) := by
  let : IsQuillenBifunctor (pointwiseTensorBifunctor (K := K)) := pointwiseTensor_isQuillen
  exact (isQuillenBifunctor_iff_pullbackHom pointwiseTensorMappingParametrizedAdjunction).1
    inferInstance

local instance enrichedModelOrdinaryCategory : EnrichedOrdinaryCategory C
    (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

/-- SM7 for Mathlib's enriched Hom functor with the chosen ordinary category. -/
lemma enrichedHom_hasQuillenPullbackHom :
    HasQuillenPullbackHom (eHomFunctor C (GeneralSymmetricSpectrum C K)) :=
  (Enriched.tensor_iff_mapping_model (spectrumTensorCotensor (K := K))).1
    pointwiseTensor_isQuillen

end SerrePositivity.GeneralSymmetricSpectrum
