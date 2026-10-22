module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinder
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutDesc

/-! # 豊穣写像円柱の同じ元の実成分
概要：円柱包含・標的包含・源比較・射影を、元の実写像円柱の射として保持する。
方針：同じ実押し出しと元の円柱の両端・射影を使う。
規約：通常射の厳密な回収。使われ方：全 Hom 自然変換と BF 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 同じ元の実円柱から写像円柱への包含。 -/
def pointedEnrichedMappingCylinderCylinder (X : C) :
    pointedTensorCylinderFunctor.obj (F.obj X) ⟶
      (pointedEnrichedMappingCylinderFunctor F G t h).obj X :=
  pointedSpanPushoutInl ((pointedEnrichedMappingCylinderSpan F G t h).obj X)

/-- 元の同じ標的から実写像円柱への包含。 -/
def pointedEnrichedMappingCylinderTarget (X : C) :
    G.obj X ⟶ (pointedEnrichedMappingCylinderFunctor F G t h).obj X :=
  pointedSpanPushoutInr ((pointedEnrichedMappingCylinderSpan F G t h).obj X)

/-- 元の同じ源から実写像円柱への比較は、区間の一端を使う。 -/
def pointedEnrichedMappingCylinderSource (X : C) :
    F.obj X ⟶ (pointedEnrichedMappingCylinderFunctor F G t h).obj X :=
  pointedTensorCylinderEnd 1 (F.obj X) ≫ pointedEnrichedMappingCylinderCylinder F G t h X

/-- 元の零端の同じ実射影は、元の射と整合する。 -/
lemma pointedEnrichedMappingCylinder_projection_condition (X : C) :
    pointedTensorCylinderEnd 0 (F.obj X) ≫ (pointedTensorCylinderProjection (F.obj X) ≫ t X) =
      t X ≫ 𝟙 (G.obj X) := by
  rw [← Category.assoc, pointedTensorCylinderEnd_projection, Category.id_comp, Category.comp_id]

/-- 同じ元の実写像円柱から元の標的への射影。 -/
def pointedEnrichedMappingCylinderProjection (X : C) :
    (pointedEnrichedMappingCylinderFunctor F G t h).obj X ⟶ G.obj X :=
  pointedSpanPushoutDesc ((pointedEnrichedMappingCylinderSpan F G t h).obj X) (G.obj X)
    (pointedTensorCylinderProjection (F.obj X) ≫ t X) (𝟙 (G.obj X))
    (pointedEnrichedMappingCylinder_projection_condition F G t X)

/-- 円柱包含は、同じ元の点つき押し出し射そのもの。 -/
lemma pointedEnrichedMappingCylinderCylinder_eq (X : C) :
    (show (pointedTensorInterval.{u} ⊗ (F.obj X).obj) ⟶
      ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj from
        pointedEnrichedMappingCylinderCylinder F G t h X) =
      pointedTensorMappingCylinderCylinder (show (F.obj X).obj ⟶ (G.obj X).obj from t X) := rfl

/-- 標的包含は、同じ元の点つき押し出し射そのもの。 -/
lemma pointedEnrichedMappingCylinderTarget_eq (X : C) :
    (show (G.obj X).obj ⟶ ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj from
      pointedEnrichedMappingCylinderTarget F G t h X) =
      pointedTensorMappingCylinderTarget (show (F.obj X).obj ⟶ (G.obj X).obj from t X) := rfl

/-- 源比較は、同じ元の一端を使う写像円柱の射そのもの。 -/
lemma pointedEnrichedMappingCylinderSource_eq (X : C) :
    (show (F.obj X).obj ⟶ ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj from
      pointedEnrichedMappingCylinderSource F G t h X) =
      pointedTensorMappingCylinderSource (show (F.obj X).obj ⟶ (G.obj X).obj from t X) := rfl

/-- 射影は、同じ元の実押し出し射影そのもの。 -/
lemma pointedEnrichedMappingCylinderProjection_eq (X : C) :
    (show ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj ⟶ (G.obj X).obj from
      pointedEnrichedMappingCylinderProjection F G t h X) =
      pointedTensorMappingCylinderProjection (show (F.obj X).obj ⟶ (G.obj X).obj from t X) := rfl

/-- 元の標的包含は、同じ写像円柱射影の厳密な切断。 -/
lemma pointedEnrichedMappingCylinderTarget_projection (X : C) :
    pointedEnrichedMappingCylinderTarget F G t h X ≫
      pointedEnrichedMappingCylinderProjection F G t h X = 𝟙 (G.obj X) :=
  pointedTensorMappingCylinderTarget_projection
    (show (F.obj X).obj ⟶ (G.obj X).obj from t X)

/-- 元の源比較と同じ射影の合成は、元の同じ射そのもの。 -/
lemma pointedEnrichedMappingCylinderSource_projection (X : C) :
    pointedEnrichedMappingCylinderSource F G t h X ≫
      pointedEnrichedMappingCylinderProjection F G t h X = t X :=
  pointedTensorMappingCylinderSource_projection
    (show (F.obj X).obj ⟶ (G.obj X).obj from t X)

end SerrePositivity.KST.SConstruction
