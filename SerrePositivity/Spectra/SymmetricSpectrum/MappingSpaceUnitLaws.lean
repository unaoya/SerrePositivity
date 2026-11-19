module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceComposition
public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

/-! # 基点付き写像対象の左単位の評価 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 単位を左因子へ入れた合成の評価が通常の左単位からの評価に一致するという法則。 -/
def mappingSpaceLeftUnitEvaluationLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.leftUnitEvaluationLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F

/-- 写像対象の左単位を合成した後の評価を計算する。 -/
lemma mappingSpace_left_unit_evaluation (E F : SymmetricSpectrum.{u}) :
    mappingSpaceLeftUnitEvaluationLaw E F := by
  apply RepresentedMappingEnrichment.left_unit_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F
  · exact GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_left (mappingSpaceUnit F)
      (pointedMappingSpace E F) E
  · exact mappingSpaceUnit_evaluation F
  · exact GeneralSymmetricSpectrum.pointwiseTensor_left_unit (pointedMappingSpace E F) E

/-- 写像対象の左単位則の等式。 -/
def mappingSpaceLeftUnitLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.leftUnitLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F

/-- 基点付き写像対象の合成は左単位則を満たす。 -/
lemma mappingSpace_left_unit (E F : SymmetricSpectrum.{u}) : mappingSpaceLeftUnitLaw E F :=
  RepresentedMappingEnrichment.left_unit pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F
    (mappingSpace_left_unit_evaluation E F)

/-- 単位を右因子へ入れた合成の評価が通常の右単位からの評価に一致するという法則。 -/
def mappingSpaceRightUnitEvaluationLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.rightUnitEvaluationLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F

/-- 写像対象の右単位を合成した後の評価を計算する。 -/
lemma mappingSpace_right_unit_evaluation (E F : SymmetricSpectrum.{u}) :
    mappingSpaceRightUnitEvaluationLaw E F := by
  apply RepresentedMappingEnrichment.right_unit_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F
  · exact GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_right (pointedMappingSpace E F)
      (mappingSpaceUnit E) E
  · exact mappingSpaceUnit_evaluation E
  · exact GeneralSymmetricSpectrum.pointwiseTensor_triangle (pointedMappingSpace E F) E

/-- 写像対象の右単位則の等式。 -/
def mappingSpaceRightUnitLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  RepresentedMappingEnrichment.rightUnitLaw pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F

/-- 基点付き写像対象の合成は右単位則を満たす。 -/
lemma mappingSpace_right_unit (E F : SymmetricSpectrum.{u}) : mappingSpaceRightUnitLaw E F :=
  RepresentedMappingEnrichment.right_unit pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} pointwiseTensorUnitNatIso.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F
    (mappingSpace_right_unit_evaluation E F)

end SerrePositivity.SymmetricSpectrum
