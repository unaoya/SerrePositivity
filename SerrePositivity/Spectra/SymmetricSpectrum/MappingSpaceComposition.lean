module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpace
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorCoherence

/-! # 基点付き写像対象の合成・単位と通常の射との対応 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 二つの写像対象をテンソルした作用から、評価を二回適用する射。 -/
def mappingSpaceCompositionEvaluation (E F G : SymmetricSpectrum.{u}) :
    pointwiseTensor (pointedMappingSpace F G ⊗ pointedMappingSpace E F) E ⟶ G :=
  (pointwiseTensorAssociator (pointedMappingSpace F G) (pointedMappingSpace E F) E).hom ≫
    (pointwiseTensorFunctor (pointedMappingSpace F G)).map (mappingSpaceEvaluation E F) ≫
      mappingSpaceEvaluation F G

/-- 基点付き写像対象の合成。後から適用する写像を左因子に置く。 -/
def mappingSpaceComposition (E F G : SymmetricSpectrum.{u}) :
    pointedMappingSpace F G ⊗ pointedMappingSpace E F ⟶ pointedMappingSpace E G :=
  mappingSpaceCurry _ (mappingSpaceCompositionEvaluation E F G)

/-- 合成を作用へ送って評価すると二回の評価に一致するという法則。 -/
def mappingSpaceCompositionEvaluationLaw (E F G : SymmetricSpectrum.{u}) : Prop :=
  AdjunctionHomLaws.curryEvaluationLaw (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E F G)

/-- 写像対象の合成は二回の評価を表現する。 -/
lemma mappingSpaceComposition_evaluation (E F G : SymmetricSpectrum.{u}) :
    mappingSpaceCompositionEvaluationLaw E F G :=
  AdjunctionHomLaws.curry_evaluation (pointedMappingSpaceAdjunction E)
    (mappingSpaceCompositionEvaluation E F G)

/-- 作用の単位比較を転置して得る写像対象の単位。 -/
def mappingSpaceUnit (E : SymmetricSpectrum.{u}) :
    𝟙_ PointedSimplicialSet.{u} ⟶ pointedMappingSpace E E :=
  mappingSpaceCurry _ (pointwiseTensorUnitIso E).hom

/-- 写像対象の単位を作用へ送って評価すると作用の単位比較になるという法則。 -/
def mappingSpaceUnitEvaluationLaw (E : SymmetricSpectrum.{u}) : Prop :=
  AdjunctionHomLaws.curryEvaluationLaw (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E).hom

/-- 写像対象の単位は作用の単位比較を表現する。 -/
lemma mappingSpaceUnit_evaluation (E : SymmetricSpectrum.{u}) :
    mappingSpaceUnitEvaluationLaw E :=
  AdjunctionHomLaws.curry_evaluation (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E).hom

/-- 通常のスペクトル射と写像対象の単位からの射の同値。 -/
def mappingSpaceArrowEquiv (E F : SymmetricSpectrum.{u}) :
    (E ⟶ F) ≃ (𝟙_ PointedSimplicialSet.{u} ⟶ pointedMappingSpace E F) :=
  AdjunctionHomLaws.comparisonHomEquiv (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E) F

/-- 通常のスペクトル射を写像対象の点へ送る。 -/
def mappingSpaceArrow {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    𝟙_ PointedSimplicialSet.{u} ⟶ pointedMappingSpace E F := mappingSpaceArrowEquiv E F f

/-- 写像対象の点から通常のスペクトル射を得る。 -/
def mappingSpaceArrowInverse {E F : SymmetricSpectrum.{u}}
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ pointedMappingSpace E F) : E ⟶ F :=
  (mappingSpaceArrowEquiv E F).symm f

/-- 恒等射の対応先は作用の単位比較の転置という法則。 -/
def mappingSpaceArrowIdentityLaw (E : SymmetricSpectrum.{u}) : Prop :=
  AdjunctionHomLaws.comparisonHomIdentityLaw (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E)

/-- 恒等射は写像対象の単位に対応する。 -/
lemma mappingSpaceArrow_identity (E : SymmetricSpectrum.{u}) : mappingSpaceArrowIdentityLaw E :=
  AdjunctionHomLaws.comparisonHomEquiv_id (pointedMappingSpaceAdjunction E)
    (pointwiseTensorUnitIso E)

end SerrePositivity.SymmetricSpectrum
