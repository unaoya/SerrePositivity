module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 同じ実写像円柱の比較を束ねた厳密豊穣自然変換
概要：全 Hom に自然な元の円柱包含・標的包含・源比較・射影を自然変換に束ねる。
方針：同じ通常成分を単位パラメータで表示する。
規約：成分も全入力族も変更しない。使われ方：厳密 dg 入力上の関手的 BF 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 同じ円柱包含を成分とする厳密豊穣自然変換。 -/
def pointedEnrichedMappingCylinderCylinderTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (F.comp SSet pointedTensorCylinderFunctor) (pointedEnrichedMappingCylinderFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMappingCylinderCylinder F G t h)
    (pointedEnrichedMappingCylinderCylinder_whisker F G t h)

/-- 同じ標的包含を成分とする厳密豊穣自然変換。 -/
def pointedEnrichedMappingCylinderTargetTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G
      (pointedEnrichedMappingCylinderFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMappingCylinderTarget F G t h)
    (pointedEnrichedMappingCylinderTarget_whisker F G t h)

/-- 同じ一端を使う源比較を成分とする厳密豊穣自然変換。 -/
def pointedEnrichedMappingCylinderSourceTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F
      (pointedEnrichedMappingCylinderFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMappingCylinderSource F G t h)
    (pointedEnrichedMappingCylinderSource_whisker F G t h)

/-- 同じ実射影を成分とする厳密豊穣自然変換。 -/
def pointedEnrichedMappingCylinderProjectionTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (pointedEnrichedMappingCylinderFunctor F G t h) G :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMappingCylinderProjection F G t h)
    (pointedEnrichedMappingCylinderProjection_whisker F G t h)

/-- 円柱包含の成分は元の同じ実射そのもの。 -/
lemma pointedEnrichedMappingCylinderCylinderTransformation_app (X : C) :
    (pointedEnrichedMappingCylinderCylinderTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMappingCylinderCylinder F G t h X) := rfl

/-- 標的包含の成分は元の同じ実射そのもの。 -/
lemma pointedEnrichedMappingCylinderTargetTransformation_app (X : C) :
    (pointedEnrichedMappingCylinderTargetTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMappingCylinderTarget F G t h X) := rfl

/-- 源比較の成分は元の同じ実射そのもの。 -/
lemma pointedEnrichedMappingCylinderSourceTransformation_app (X : C) :
    (pointedEnrichedMappingCylinderSourceTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMappingCylinderSource F G t h X) := rfl

/-- 射影の成分は元の同じ実射そのもの。 -/
lemma pointedEnrichedMappingCylinderProjectionTransformation_app (X : C) :
    (pointedEnrichedMappingCylinderProjectionTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMappingCylinderProjection F G t h X) := rfl

end SerrePositivity.KST.SConstruction
