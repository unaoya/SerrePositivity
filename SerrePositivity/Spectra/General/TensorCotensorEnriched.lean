module

public import SerrePositivity.Spectra.General.MappingFunctorComparison
public import SerrePositivity.Spectra.General.ParametrizedCotensor
public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor

/-! # The represented tensor/cotensor receiver for general symmetric spectra -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

local instance : EnrichedOrdinaryCategory C (GeneralSymmetricSpectrum C K) :=
  mappingEnrichedOrdinaryCategory

/-- The existing C action and cotensor represent Mathlib's enriched Hom functor. -/
def spectrumTensorCotensor : Enriched.TensorCotensor C (GeneralSymmetricSpectrum C K) where
  tensor := pointwiseTensorBifunctor
  cotensor := cotensorBifunctor
  tensorCotensor := pointwiseTensorCotensorParametrizedAdjunction
  tensorHom := ParametrizedAdjunctionTransport.right
    pointwiseTensorMappingParametrizedAdjunction mappingEnrichedHomFunctorIso.symm

/-- The enriched-Hom comparison has identity components, so generalized points
use the previously constructed mapping-object Hom equivalence. -/
lemma spectrumTensorCotensor_tensorHomEquiv (X : C)
    (E F : GeneralSymmetricSpectrum C K) (f : pointwiseTensor X E ⟶ F) :
    spectrumTensorCotensor.tensorHomEquiv X E F f = mappingObjectHomEquiv X E F f := by
  change ((mappingObjectAdjunction E).ofNatIsoRight
    (mappingEnrichedHomFunctorIso.symm.app (Opposite.op E))).homEquiv X F f = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change mappingObjectHomEquiv X E F f ≫ 𝟙 _ = _
  exact Category.comp_id _

end SerrePositivity.GeneralSymmetricSpectrum
