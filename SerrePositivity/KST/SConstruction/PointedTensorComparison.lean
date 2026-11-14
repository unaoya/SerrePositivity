module
public import SerrePositivity.KST.SConstruction.PointedTensorEnrichedFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationWhisker

/-! # 同じ全 Hom 自然な比較の左 smash
概要：任意の元の全 Hom 自然な比較を、固定左因子との同じ smash で保持する。
方針：元の厳密豊穣変換を後合成し、同じ通常成分の回収式を使う。
規約：実際の前向き射を保つ。使われ方：B_(n−1)→K_n の suspension 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (K : PointedSimplicialSet.{u}) (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (c : ∀ X, F.obj X ⟶ G.obj X)
  (hc : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (c Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (c X) (G.obj Y))

/-- 同じ元の比較を左 smash した厳密豊穣自然変換。 -/
def pointedTensorComparisonTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (F.comp SSet (pointedTensorEnrichedFunctor K))
      (G.comp SSet (pointedTensorEnrichedFunctor K)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose F G (pointedTensorEnrichedFunctor K)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker F G c hc)

/-- 同じ比較の左 smash は、元の同じ通常射を成分に持つ。 -/
lemma pointedTensorComparisonTransformation_app (X : C) :
    (pointedTensorComparisonTransformation K F G c hc).app X =
      eHomEquiv SSet
        (show (F.comp SSet (pointedTensorEnrichedFunctor K)).obj X ⟶
          (G.comp SSet (pointedTensorEnrichedFunctor K)).obj X from
            K ◁ (show (F.obj X).obj ⟶ (G.obj X).obj from c X)) :=
  pointedTensorEnrichedFunctor_hom K (c X)

include hc in
/-- 元の比較の同じ左 smash は、全 Hom に厳密に自然。 -/
lemma pointedTensorComparison_whisker (X Y : C) :
    (F.comp SSet (pointedTensorEnrichedFunctor K)).map X Y ≫
        eHomWhiskerLeft SSet ((F.comp SSet (pointedTensorEnrichedFunctor K)).obj X)
          (show (F.comp SSet (pointedTensorEnrichedFunctor K)).obj Y ⟶
            (G.comp SSet (pointedTensorEnrichedFunctor K)).obj Y from
              K ◁ (show (F.obj Y).obj ⟶ (G.obj Y).obj from c Y)) =
      (G.comp SSet (pointedTensorEnrichedFunctor K)).map X Y ≫
        eHomWhiskerRight SSet
          (show (F.comp SSet (pointedTensorEnrichedFunctor K)).obj X ⟶
            (G.comp SSet (pointedTensorEnrichedFunctor K)).obj X from
              K ◁ (show (F.obj X).obj ⟶ (G.obj X).obj from c X))
          ((G.comp SSet (pointedTensorEnrichedFunctor K)).obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (pointedTensorComparisonTransformation K F G c hc) _
    (pointedTensorComparisonTransformation_app K F G c hc) X Y

end SerrePositivity.KST.SConstruction
