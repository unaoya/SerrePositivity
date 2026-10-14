module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceEnriched

/-! # 基点付き豊穣構造と既存のスペクトルの圏構造の一致 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory

/-- 基点付き写像対象の豊穣構造を既存の通常の圏構造へ接続する。 -/
@[instance_reducible]
def pointedMappingEnrichedOrdinaryCategory :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
  RepresentedMappingEnrichment.ordinaryCategory pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u}
    mappingSpace_left_unit.{u} mappingSpace_right_unit.{u} mappingSpace_associativity.{u}
    mappingSpaceArrow_identity.{u} mappingSpaceArrow_composition.{u}

end SerrePositivity.SymmetricSpectrum
