module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceUnitLaws
public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

/-! # 基点付き写像対象の合成の結合則 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 三つの写像対象の反復合成を評価した射が等しいという法則。 -/
def mappingSpaceAssociativityEvaluationLaw (E F G K : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.associativityEvaluationLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointedMappingSpaceFunctor.{u}
    pointedMappingSpaceAdjunction.{u} E F G K

/-- 反復合成の二つの経路は評価後に一致する。 -/
lemma mappingSpace_associativity_evaluation (E F G K : SymmetricSpectrum.{u}) :
    mappingSpaceAssociativityEvaluationLaw E F G K := by
  apply RepresentedMappingEnrichment.associativity_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointedMappingSpaceFunctor.{u}
    pointedMappingSpaceAdjunction.{u} E F G K
  · exact GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_left (mappingSpaceComposition F G K)
      (pointedMappingSpace E F) E
  · exact GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_right (pointedMappingSpace G K)
      (mappingSpaceComposition E F G) E
  · exact GeneralSymmetricSpectrum.pointwiseTensorBifunctor_pentagon (K := circle.{u})
      (pointedMappingSpace G K) (pointedMappingSpace F G) (pointedMappingSpace E F) E

/-- 基点付き写像対象の合成の結合則の等式。 -/
def mappingSpaceAssociativityLaw (E F G K : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.associativityLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointedMappingSpaceFunctor.{u}
    pointedMappingSpaceAdjunction.{u} E F G K

/-- 基点付き写像対象の合成は結合則を満たす。 -/
lemma mappingSpace_associativity (E F G K : SymmetricSpectrum.{u}) :
    mappingSpaceAssociativityLaw E F G K :=
  RepresentedMappingEnrichment.associativity pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointedMappingSpaceFunctor.{u}
    pointedMappingSpaceAdjunction.{u} E F G K
    (mappingSpace_associativity_evaluation E F G K)

end SerrePositivity.SymmetricSpectrum
