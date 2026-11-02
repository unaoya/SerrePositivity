module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceSimplicial
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence
public import SerrePositivity.CategoryTheory.Enriched.Transport

/-! # 基点付き写像対象による豊穣圏 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory

/-- 最初に適用する射を第一因子に置いた基点付き写像対象の合成。 -/
def pointedMappingComposition (E F G : SymmetricSpectrum.{u}) :
    pointedMappingSpace E F ⊗ pointedMappingSpace F G ⟶ pointedMappingSpace E G :=
  ReverseComposition.reverse (mappingSpaceComposition E F G)

/-- 既存の写像対象の合成・単位・結合則による基点付き豊穣圏。 -/
@[instance_reducible]
def pointedMappingEnrichedCategory :
    EnrichedCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
  RepresentedMappingEnrichment.enrichedCategory pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u}
    mappingSpace_left_unit.{u} mappingSpace_right_unit.{u} mappingSpace_associativity.{u}

/-- 基点付き豊穣構造の合成は既存の合成の因子を交換したもの。 -/
lemma pointedMappingEnrichedCategory_comp (E F G : SymmetricSpectrum.{u}) :
    pointedMappingEnrichedCategory.comp E F G =
      ReverseComposition.reverse (mappingSpaceComposition E F G) :=
  RepresentedMappingEnrichment.enrichedCategory_comp pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u}
    mappingSpace_left_unit.{u} mappingSpace_right_unit.{u} mappingSpace_associativity.{u} E F G

/-- 基点付き豊穣構造の単位は既存の写像対象の単位。 -/
lemma pointedMappingEnrichedCategory_id (E : SymmetricSpectrum.{u}) :
    pointedMappingEnrichedCategory.id E = mappingSpaceUnit E :=
  RepresentedMappingEnrichment.enrichedCategory_id pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u}
    mappingSpace_left_unit.{u} mappingSpace_right_unit.{u} mappingSpace_associativity.{u} E

end SerrePositivity.SymmetricSpectrum
