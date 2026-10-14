module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceComposition
public import SerrePositivity.CategoryTheory.Monoidal.MappingUnitLaws

/-! # 基点付き写像対象の左単位の評価 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 単位を左因子へ入れた合成の評価が、通常の左単位からの評価に一致するという法則。 -/
def mappingSpaceLeftUnitEvaluationLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  (mappingTensorFunctor E).map (mappingSpaceUnit F ⊗ₘ 𝟙 (pointedMappingSpace E F)) ≫
    mappingSpaceCompositionEvaluation E F F =
  (mappingTensorFunctor E).map (λ_ (pointedMappingSpace E F)).hom ≫
    mappingSpaceEvaluation E F

/-- 写像対象の左単位を合成した後の評価を計算する。 -/
lemma mappingSpace_left_unit_evaluation (E F : SymmetricSpectrum.{u}) :
    mappingSpaceLeftUnitEvaluationLaw E F := by
  apply MappingUnitLaws.left_unit_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorUnitNatIso.{u} (mappingSpaceUnit F) (mappingSpaceEvaluation E F)
    (mappingSpaceEvaluation F F)
    (pointwiseTensorAssociator (pointedMappingSpace F F) (pointedMappingSpace E F) E).hom
    (pointwiseTensorAssociator (𝟙_ PointedSimplicialSet.{u})
      (pointedMappingSpace E F) E).hom
  · exact pointwiseTensorAssociator_parameter_left (mappingSpaceUnit F)
      (pointedMappingSpace E F) E
  · exact mappingSpaceUnit_evaluation F
  · exact pointwiseTensor_left_unit (pointedMappingSpace E F) E

/-- 写像対象の左単位則の等式。 -/
def mappingSpaceLeftUnitLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E F F)
    (mappingSpaceUnit F ⊗ₘ 𝟙 (pointedMappingSpace E F))
    (λ_ (pointedMappingSpace E F)).hom

/-- 基点付き写像対象の合成は左単位則を満たす。 -/
lemma mappingSpace_left_unit (E F : SymmetricSpectrum.{u}) : mappingSpaceLeftUnitLaw E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E F F)
    (mappingSpaceUnit F ⊗ₘ 𝟙 (pointedMappingSpace E F))
    (λ_ (pointedMappingSpace E F)).hom (mappingSpace_left_unit_evaluation E F)

/-- 単位を右因子へ入れた合成の評価が、通常の右単位からの評価に一致するという法則。 -/
def mappingSpaceRightUnitEvaluationLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  (mappingTensorFunctor E).map (𝟙 (pointedMappingSpace E F) ⊗ₘ mappingSpaceUnit E) ≫
    mappingSpaceCompositionEvaluation E E F =
  (mappingTensorFunctor E).map (ρ_ (pointedMappingSpace E F)).hom ≫
    mappingSpaceEvaluation E F

/-- 写像対象の右単位を合成した後の評価を計算する。 -/
lemma mappingSpace_right_unit_evaluation (E F : SymmetricSpectrum.{u}) :
    mappingSpaceRightUnitEvaluationLaw E F := by
  apply MappingUnitLaws.right_unit_evaluation pointwiseTensorBifunctor.{u}
    pointwiseTensorUnitNatIso.{u} (mappingSpaceUnit E) (mappingSpaceEvaluation E F)
    (mappingSpaceEvaluation E E)
    (pointwiseTensorAssociator (pointedMappingSpace E F) (pointedMappingSpace E E) E).hom
    (pointwiseTensorAssociator (pointedMappingSpace E F)
      (𝟙_ PointedSimplicialSet.{u}) E).hom
  · exact pointwiseTensorAssociator_parameter_right (pointedMappingSpace E F)
      (mappingSpaceUnit E) E
  · exact mappingSpaceUnit_evaluation E
  · exact pointwiseTensor_triangle (pointedMappingSpace E F) E

/-- 写像対象の右単位則の等式。 -/
def mappingSpaceRightUnitLaw (E F : SymmetricSpectrum.{u}) : Prop :=
  AdjunctionHomLaws.curryPreEqualityLaw (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E E F)
    (𝟙 (pointedMappingSpace E F) ⊗ₘ mappingSpaceUnit E)
    (ρ_ (pointedMappingSpace E F)).hom

/-- 基点付き写像対象の合成は右単位則を満たす。 -/
lemma mappingSpace_right_unit (E F : SymmetricSpectrum.{u}) : mappingSpaceRightUnitLaw E F :=
  AdjunctionHomLaws.curry_pre_eq_of_evaluation (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E E F)
    (𝟙 (pointedMappingSpace E F) ⊗ₘ mappingSpaceUnit E)
    (ρ_ (pointedMappingSpace E F)).hom (mappingSpace_right_unit_evaluation E F)

end SerrePositivity.SymmetricSpectrum
