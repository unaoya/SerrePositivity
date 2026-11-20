module

public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFunctor
public import SerrePositivity.Spectra.General.ParametrizedCotensor
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

/-! # 基点付き写像対象と各段のsmashの表現性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor pointwiseTensorPost tensorFreeZeroPointwiseIso)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 基点付き写像対象は原変数に反変、値域に共変な二変数関手。 -/
abbrev pointedMappingSpaceBifunctor :=
  GeneralSymmetricSpectrum.mappingObjectBifunctor (K := circle.{u})

/-- 各段のsmashと写像対象の、スペクトル変数に関して自然な随伴。 -/
abbrev pointedMappingSpaceParametrizedAdjunction :=
  MonoidalMappingAdjunction.transportedParametrizedAdjunction (freeAtAdjunction.{u} 0)
    pointwiseTensorBifunctor.{u} GeneralSymmetricSpectrum.mappingTensorNatIso
    (fun {_ _} f X ↦ (GeneralSymmetricSpectrum.tensorFreeZeroPointwiseNatIso X).hom.naturality f)

end SerrePositivity.SymmetricSpectrum
