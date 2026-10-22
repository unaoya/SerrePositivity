module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderTransformation

/-! # 同じ元の円柱射と両端・射影の通常自然性
概要：元の点つき射を左 smash した同じ円柱射と、元の両端・射影の自然性を回収する。
方針：左 tensor の全 Hom の頂点回収と、二因子交換および左単位子の自然性を使う。
規約：通常射も同じ元の射を保持。使われ方：実写像円柱の可換正方形への作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 円柱の全 Hom 作用は、元の通常射の同じ左 smash を回収する。 -/
lemma pointedTensorCylinderFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ pointedTensorCylinderFunctor.map X Y =
      eHomEquiv SSet
        (show pointedTensorCylinderFunctor.obj X ⟶ pointedTensorCylinderFunctor.obj Y from
          pointedTensorInterval.{u} ◁ (show X.obj ⟶ Y.obj from f)) :=
  pointedTensorEnrichedFunctor_hom pointedTensorInterval.{u} (X := X) (Y := Y) f

/-- 元の円柱端点は、元の全通常射について同じ左 smash に自然。 -/
lemma pointedTensorCylinderEnd_naturality (i : Fin 2)
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorCylinderEndMap i X ≫ pointedTensorInterval.{u} ◁ f =
      f ≫ pointedTensorCylinderEndMap i Y := by
  change ((λ_ X).inv ≫ pointedTensorIntervalEnd i ▷ X) ≫ pointedTensorInterval.{u} ◁ f =
    f ≫ (λ_ Y).inv ≫ pointedTensorIntervalEnd i ▷ Y
  rw [Category.assoc, ← whisker_exchange, ← Category.assoc, ← leftUnitor_inv_naturality,
    Category.assoc]

/-- 元の円柱射影は、元の全通常射について同じ左 smash に自然。 -/
lemma pointedTensorCylinderProjection_naturality
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorInterval.{u} ◁ f ≫
        pointedTensorCylinderProjectionMap Y =
      pointedTensorCylinderProjectionMap X ≫ f := by
  change pointedTensorInterval.{u} ◁ f ≫
      (pointedTensorIntervalProjection ▷ Y ≫ (λ_ Y).hom) =
    (pointedTensorIntervalProjection ▷ X ≫ (λ_ X).hom) ≫ f
  rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality,
    Category.assoc]

end SerrePositivity.KST.SConstruction
