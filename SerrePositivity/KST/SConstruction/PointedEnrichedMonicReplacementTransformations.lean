module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacementNaturality

/-! # 同じ関手的 Kan 単射置換の厳密豊穣比較
概要：元の単位と源・標的比較を、同じ全 Hom 自然な豊穣変換へ束ねる。
方針：元の通常成分の単位パラメータ表示を使う。
規約：実成分も高次入力も変更しない。使われ方：BF 全段の厳密豊穣構造。
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

/-- 同じ元の Unit 比較を成分とする厳密豊穣変換。 -/
def pointedEnrichedMonicReplacementUnitTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (pointedEnrichedMappingCylinderFunctor F G t h)
      (pointedEnrichedMonicReplacementFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMonicReplacementUnit F G t h)
    (pointedEnrichedMonicReplacementUnit_whisker F G t h)

/-- 豊穣変換の成分は、同じ元の Unit 比較を回収する。 -/
lemma pointedEnrichedMonicReplacementUnitTransformation_app (X : C) :
    (pointedEnrichedMonicReplacementUnitTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMonicReplacementUnit F G t h X) := rfl

/-- 同じ元の Source 比較を成分とする厳密豊穣変換。 -/
def pointedEnrichedMonicReplacementSourceTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F
      (pointedEnrichedMonicReplacementFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMonicReplacementSource F G t h)
    (pointedEnrichedMonicReplacementSource_whisker F G t h)

/-- 豊穣変換の成分は、同じ元の Source 比較を回収する。 -/
lemma pointedEnrichedMonicReplacementSourceTransformation_app (X : C) :
    (pointedEnrichedMonicReplacementSourceTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMonicReplacementSource F G t h X) := rfl

/-- 同じ元の Target 比較を成分とする厳密豊穣変換。 -/
def pointedEnrichedMonicReplacementTargetTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G
      (pointedEnrichedMonicReplacementFunctor F G t h) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (pointedEnrichedMonicReplacementTarget F G t h)
    (pointedEnrichedMonicReplacementTarget_whisker F G t h)

/-- 豊穣変換の成分は、同じ元の Target 比較を回収する。 -/
lemma pointedEnrichedMonicReplacementTargetTransformation_app (X : C) :
    (pointedEnrichedMonicReplacementTargetTransformation F G t h).app X =
      eHomEquiv SSet (pointedEnrichedMonicReplacementTarget F G t h X) := rfl

end SerrePositivity.KST.SConstruction
