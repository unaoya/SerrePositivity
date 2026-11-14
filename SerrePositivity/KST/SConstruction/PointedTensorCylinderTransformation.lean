module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinder
public import SerrePositivity.KST.SConstruction.PointedTensorTransformations
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationComposition
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationWhisker

/-! # 元の点つき円柱の両端・射影の厳密豊穣自然変換
概要：自由点つき区間の実両端と射影を、同じ円柱関手の全 Hom に自然に束ねる。
方針：左 tensor パラメータの自然変換と左右の元の単位同型を合成する。
規約：同じ元の通常成分を回収する。使われ方：写像円柱の厳密豊穣関手化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の円柱の指定端点を成分とする、全 Hom の厳密豊穣自然変換。 -/
def pointedTensorCylinderEndTransformation (i : Fin 2) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u}) pointedTensorCylinderFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp _ _ _ pointedTensorLeftUnitorInvTransformation
    (pointedTensorParameterTransformation (pointedTensorIntervalEnd i))

/-- 元の円柱の射影を成分とする、全 Hom の厳密豊穣自然変換。 -/
def pointedTensorCylinderProjectionTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) pointedTensorCylinderFunctor
      (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp _ _ _
    (pointedTensorParameterTransformation pointedTensorIntervalProjection)
    pointedTensorLeftUnitorTransformation

/-- 全 Hom の端点自然変換の成分は、元の同じ端点射そのもの。 -/
lemma pointedTensorCylinderEndTransformation_app (i : Fin 2) (X : PointedSSetObject.{u}) :
    (pointedTensorCylinderEndTransformation i).app X =
      eHomEquiv SSet (pointedTensorCylinderEnd i X) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp_hom
    (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u})
    (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u}))
    pointedTensorCylinderFunctor pointedTensorLeftUnitorInvTransformation
    (pointedTensorParameterTransformation (pointedTensorIntervalEnd i)) X
    (show X ⟶ (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X from
      (λ_ X.obj).inv)
    (show (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X ⟶
      pointedTensorCylinderFunctor.obj X from pointedTensorIntervalEnd i ▷ X.obj) rfl rfl

/-- 全 Hom の射影自然変換の成分は、元の同じ射影そのもの。 -/
lemma pointedTensorCylinderProjectionTransformation_app (X : PointedSSetObject.{u}) :
    pointedTensorCylinderProjectionTransformation.app X =
      eHomEquiv SSet (pointedTensorCylinderProjection X) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp_hom pointedTensorCylinderFunctor
    (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u}))
    (EnrichedFunctor.id SSet.{u} PointedSSetObject.{u})
    (pointedTensorParameterTransformation pointedTensorIntervalProjection)
    pointedTensorLeftUnitorTransformation X
    (show pointedTensorCylinderFunctor.obj X ⟶
      (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X from
      pointedTensorIntervalProjection ▷ X.obj)
    (show (pointedTensorEnrichedFunctor (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X from
      (λ_ X.obj).hom) rfl rfl

/-- 元の指定端点は、円柱関手の全 Hom 作用に厳密に自然。 -/
lemma pointedTensorCylinderEnd_whisker (i : Fin 2) (X Y : PointedSSetObject.{u}) :
    eHomWhiskerLeft SSet X (pointedTensorCylinderEnd i Y) =
      pointedTensorCylinderFunctor.map X Y ≫
        eHomWhiskerRight SSet (pointedTensorCylinderEnd i X)
          (pointedTensorCylinderFunctor.obj Y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (pointedTensorCylinderEndTransformation i) (pointedTensorCylinderEnd i)
    (pointedTensorCylinderEndTransformation_app i) X Y
  change 𝟙 (X ⟶[SSet.{u}] Y) ≫ _ = _ at h
  erw [Category.id_comp] at h
  exact h

/-- 元の射影は、円柱関手の全 Hom 作用に厳密に自然。 -/
lemma pointedTensorCylinderProjection_whisker (X Y : PointedSSetObject.{u}) :
    pointedTensorCylinderFunctor.map X Y ≫
        eHomWhiskerLeft SSet (pointedTensorCylinderFunctor.obj X)
          (pointedTensorCylinderProjection Y) =
      eHomWhiskerRight SSet (pointedTensorCylinderProjection X) Y := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    pointedTensorCylinderProjectionTransformation pointedTensorCylinderProjection
    pointedTensorCylinderProjectionTransformation_app X Y
  change _ = 𝟙 (X ⟶[SSet.{u}] Y) ≫ _ at h
  erw [Category.id_comp] at h
  exact h

end SerrePositivity.KST.SConstruction
