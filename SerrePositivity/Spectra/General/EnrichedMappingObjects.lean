module

public import SerrePositivity.Spectra.General.TensorMappingSource
public import SerrePositivity.Spectra.General.CotensorMappingSource
public import SerrePositivity.CategoryTheory.Enriched.EnrichedRepresentability
public import Mathlib.CategoryTheory.Whiskering

/-! # Natural isomorphisms of enriched tensor/cotensor Hom objects

These are natural in both spectrum variables. Parameter variance and the
compatibility with ordinary points are separate representability obligations.
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

/-- Tensor Hom-object representability on the existing enriched category. -/
def tensorEnrichedMappingIso (X : C) :
    Enriched.tensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X :=
  Functor.isoWhiskerLeft (pointwiseTensorFunctor X).op mappingEnrichedHomFunctorIso ≪≫
    tensorMappingBifunctorIso X ≪≫
      Functor.isoWhiskerRight mappingEnrichedHomFunctorIso.symm
        ((Functor.whiskeringRight _ _ _).obj (ihom X))

/-- Cotensor Hom-object representability on the existing enriched category. -/
def cotensorEnrichedMappingIso (X : C) :
    Enriched.cotensorEnrichedHom (spectrumTensorCotensor (K := K)) X ≅
      Enriched.powerHom (C := GeneralSymmetricSpectrum C K) X :=
  Functor.isoWhiskerRight mappingEnrichedHomFunctorIso
    ((Functor.whiskeringLeft _ _ _).obj (cotensorFunctor X)) ≪≫
    cotensorMappingBifunctorIso X ≪≫
      Functor.isoWhiskerRight mappingEnrichedHomFunctorIso.symm
        ((Functor.whiskeringRight _ _ _).obj (ihom X))

end SerrePositivity.GeneralSymmetricSpectrum
