module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceUnitLaws
public import SerrePositivity.CategoryTheory.Monoidal.MappingAssociativity

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
  MappingAssociativity.associativityEvaluationLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u}
    (mappingSpaceComposition F G K) (mappingSpaceComposition E F G)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation G K)
    (mappingSpaceEvaluation F K) (mappingSpaceEvaluation E G)

/-- 反復合成の二つの経路は評価後に一致する。 -/
lemma mappingSpace_associativity_evaluation (E F G K : SymmetricSpectrum.{u}) :
    mappingSpaceAssociativityEvaluationLaw E F G K := by
  apply MappingAssociativity.associativity_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u}
    (mappingSpaceComposition F G K) (mappingSpaceComposition E F G)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation F G) (mappingSpaceEvaluation G K)
    (mappingSpaceEvaluation F K) (mappingSpaceEvaluation E G)
  · exact mappingSpaceComposition_evaluation F G K
  · exact mappingSpaceComposition_evaluation E F G
  · exact pointwiseTensorAssociator_parameter_left (mappingSpaceComposition F G K)
      (pointedMappingSpace E F) E
  · exact pointwiseTensorAssociator_parameter_right (pointedMappingSpace G K)
      (mappingSpaceComposition E F G) E
  · exact pointwiseTensor_pentagon (pointedMappingSpace G K) (pointedMappingSpace F G)
      (pointedMappingSpace E F) E

/-- 基点付き写像対象の合成の結合則の等式。 -/
def mappingSpaceAssociativityLaw (E F G K : SymmetricSpectrum.{u}) : Prop :=
  MappingAssociativity.representedAssociativityLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} (pointedMappingSpaceAdjunction E)
    (mappingSpaceComposition F G K) (mappingSpaceComposition E F G)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation G K)
    (mappingSpaceEvaluation F K) (mappingSpaceEvaluation E G)

/-- 基点付き写像対象の合成は結合則を満たす。 -/
lemma mappingSpace_associativity (E F G K : SymmetricSpectrum.{u}) :
    mappingSpaceAssociativityLaw E F G K :=
  MappingAssociativity.represented_associativity pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} (pointedMappingSpaceAdjunction E)
    (mappingSpaceComposition F G K) (mappingSpaceComposition E F G)
    (mappingSpaceEvaluation E F) (mappingSpaceEvaluation G K)
    (mappingSpaceEvaluation F K) (mappingSpaceEvaluation E G)
    (mappingSpace_associativity_evaluation E F G K)

end SerrePositivity.SymmetricSpectrum
