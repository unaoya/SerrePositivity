module
public import SerrePositivity.KST.SConstruction.PointedTensorEnrichedFunctor
public import SerrePositivity.KST.SConstruction.ClosedTensorMappingUnit
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker

/-! # 左 smash パラメータと単位子の厳密豊穣自然性
概要：固定左因子の射と左単位同型を、全 basedHom の自然変換として保持する。
方針：閉 Hom の全 tensor 作用の式を、元の標準点つき前後合成へ移す。
規約：高次入力を頂点へ制限しない。使われ方：関手的点つき円柱の両端と射影。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- 左因子の射は、全 basedHom の tensor 作用に厳密に自然。 -/
lemma pointedTensor_parameter_whisker {K L : PointedSimplicialSet.{u}} (a : K ⟶ L)
    (X Y : PointedSSetObject.{u}) :
    (pointedTensorEnrichedFunctor K).map X Y ≫
        eHomWhiskerLeft SSet ((pointedTensorEnrichedFunctor K).obj X)
          (show (pointedTensorEnrichedFunctor K).obj Y ⟶
            (pointedTensorEnrichedFunctor L).obj Y from a ▷ Y.obj) =
      (pointedTensorEnrichedFunctor L).map X Y ≫
        eHomWhiskerRight SSet
          (show (pointedTensorEnrichedFunctor K).obj X ⟶
            (pointedTensorEnrichedFunctor L).obj X from a ▷ X.obj)
          ((pointedTensorEnrichedFunctor L).obj Y) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  have h := closedTensorMapping_parameter a X.obj Y.obj
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact congrArg Under.Hom.right h

/-- 固定左因子の射は、同じ通常の左 smash 成分を持つ厳密豊穣自然変換。 -/
def pointedTensorParameterTransformation {K L : PointedSimplicialSet.{u}} (a : K ⟶ L) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (pointedTensorEnrichedFunctor K) (pointedTensorEnrichedFunctor L) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (fun X => a ▷ X.obj)
    (pointedTensor_parameter_whisker a)

/-- 元の左単位同型の全 Hom 自然性。 -/
lemma pointedTensor_leftUnitor_whisker (X Y : PointedSSetObject.{u}) :
    (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).map X Y ≫
        eHomWhiskerLeft SSet
          ((pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X)
          (show (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj Y ⟶ Y
            from (λ_ Y.obj).hom) =
      eHomWhiskerRight SSet
        (show (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X
          from (λ_ X.obj).hom) Y := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  have h := closedTensorMapping_leftUnitor X.obj Y.obj
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact congrArg Under.Hom.right h

/-- 元の逆左単位同型の全 Hom 自然性。 -/
lemma pointedTensor_leftUnitor_inv_whisker (X Y : PointedSSetObject.{u}) :
    eHomWhiskerLeft SSet X
        (show Y ⟶ (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj Y
          from (λ_ Y.obj).inv) =
      (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).map X Y ≫
        eHomWhiskerRight SSet
          (show X ⟶ (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X
            from (λ_ X.obj).inv)
          ((pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj Y) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  have h := closedTensorMapping_leftUnitor_inv X.obj Y.obj
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact congrArg Under.Hom.right h

/-- 左単位子による、固定左単位 tensor から恒等関手への厳密豊穣自然変換。 -/
def pointedTensorLeftUnitorTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u}))
      (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (fun X => (λ_ X.obj).hom)
    (by
      intro X Y
      change _ ≫ _ = 𝟙 (X ⟶[SSet.{u}] Y) ≫ _
      erw [Category.id_comp]
      exact pointedTensor_leftUnitor_whisker X Y)

/-- 逆左単位子による、恒等関手から固定左単位 tensor への厳密豊穣自然変換。 -/
def pointedTensorLeftUnitorInvTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u})
      (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (fun X => (λ_ X.obj).inv)
    (by
      intro X Y
      change 𝟙 (X ⟶[SSet.{u}] Y) ≫ _ = _ ≫ _
      erw [Category.id_comp]
      exact pointedTensor_leftUnitor_inv_whisker X Y)

end SerrePositivity.KST.SConstruction
