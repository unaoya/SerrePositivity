module

public import SerrePositivity.Spectra.General.CotensorMappingPoints

/-! # Full enriched tensor and cotensor representability of general spectra

The natural C-valued Hom-object comparisons, their parameter variance, and their
compatibility with the chosen ordinary adjunctions are packaged together.
-/

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

/-- Full Hom-object representability on the existing enriched spectrum category. -/
def spectrumEnrichedRepresentability :
    Enriched.EnrichedRepresentability (spectrumTensorCotensor (K := K)) where
  tensorIso := tensorEnrichedMappingIso
  cotensorIso := cotensorEnrichedMappingIso
  tensor_parameter := tensorEnrichedMappingIso_parameter
  cotensor_parameter := cotensorEnrichedMappingIso_parameter
  tensor_points := tensorEnrichedMappingIso_points
  cotensor_points := cotensorEnrichedMappingIso_points

/-- Comparing the two represented Hom objects is the chosen ordinary adjunction
on ordinary points. -/
lemma spectrumHomObjectComparison_points (X : C) (E F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E ⟶ F) :
    eHomEquiv C f ≫ (spectrumEnrichedRepresentability.homObjectComparison X E F).hom =
      eHomEquiv C (pointwiseTensorHomEquiv X E F f) :=
  spectrumEnrichedRepresentability.homObjectComparison_points X E F f

end SerrePositivity.GeneralSymmetricSpectrum
