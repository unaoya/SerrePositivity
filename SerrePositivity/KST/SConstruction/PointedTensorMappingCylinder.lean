module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 元の点つき円柱を押し出した実写像円柱
概要：任意の元の点つき射に対して、区間の零端を貼り付けた写像円柱を構成する。
方針：同じ点つき圏の実押し出しを使い、射影と両比較の厳密な回収を証明する。
規約：源の射の単射性を仮定しない。使われ方：BF の関手的単射置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 同じ元の点つき円柱の、点つき圏での実押し出し。 -/
def pointedTensorMappingCylinder {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    PointedSimplicialSet.{u} :=
  pushout (pointedTensorCylinderEndMap 0 X) f

/-- 元の円柱から写像円柱への実押し出し射。 -/
def pointedTensorMappingCylinderCylinder {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (pointedTensorInterval.{u} ⊗ X) ⟶ pointedTensorMappingCylinder f :=
  pushout.inl _ _

/-- 元の標的から写像円柱への実押し出し射。 -/
def pointedTensorMappingCylinderTarget {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    Y ⟶ pointedTensorMappingCylinder f :=
  pushout.inr _ _

/-- 元の源から写像円柱への比較は、元の区間の一端を使う。 -/
def pointedTensorMappingCylinderSource {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    X ⟶ pointedTensorMappingCylinder f :=
  pointedTensorCylinderEndMap 1 X ≫ pointedTensorMappingCylinderCylinder f

/-- 元の零端の貼り付け条件は、同じ元の射 f を厳密に回収する。 -/
lemma pointedTensorMappingCylinder_condition {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorCylinderEndMap 0 X ≫ pointedTensorMappingCylinderCylinder f =
      f ≫ pointedTensorMappingCylinderTarget f :=
  pushout.condition

/-- 元の零端と射影は、後に同じ f を作用させても貼り付け条件を満たす。 -/
lemma pointedTensorMappingCylinder_projection_condition
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorCylinderEndMap 0 X ≫
        (pointedTensorCylinderProjectionMap X ≫ f) = f ≫ 𝟙 Y := by
  have h : pointedTensorCylinderEndMap 0 X ≫
        pointedTensorCylinderProjectionMap X = 𝟙 X :=
    pointedTensorCylinderEndMap_projection 0 X
  rw [← Category.assoc, h, Category.id_comp, Category.comp_id]

/-- 元の区間の射影と f から得られる、元の標的への実写像円柱射影。 -/
def pointedTensorMappingCylinderProjection {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorMappingCylinder f ⟶ Y :=
  pushout.desc
    (pointedTensorCylinderProjectionMap X ≫ f) (𝟙 Y)
    (pointedTensorMappingCylinder_projection_condition f)

/-- 実円柱上では、射影は元の円柱射影の後に同じ元の f を作用させる。 -/
lemma pointedTensorMappingCylinderCylinder_projection {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    pointedTensorMappingCylinderCylinder f ≫ pointedTensorMappingCylinderProjection f =
      pointedTensorCylinderProjectionMap X ≫ f :=
  pushout.inl_desc _ _ _

/-- 元の標的包含は、同じ写像円柱射影の厳密な切断。 -/
lemma pointedTensorMappingCylinderTarget_projection {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    pointedTensorMappingCylinderTarget f ≫ pointedTensorMappingCylinderProjection f = 𝟙 Y :=
  pushout.inr_desc _ _ _

/-- 元の源比較と写像円柱射影の合成は、同じ元の f そのもの。 -/
lemma pointedTensorMappingCylinderSource_projection {X Y : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    pointedTensorMappingCylinderSource f ≫ pointedTensorMappingCylinderProjection f = f := by
  change (pointedTensorCylinderEndMap 1 X ≫ pointedTensorMappingCylinderCylinder f) ≫ _ = _
  rw [Category.assoc, pointedTensorMappingCylinderCylinder_projection, ← Category.assoc]
  have h : pointedTensorCylinderEndMap 1 X ≫
        pointedTensorCylinderProjectionMap X = 𝟙 X :=
    pointedTensorCylinderEndMap_projection 1 X
  rw [h, Category.id_comp]

end SerrePositivity.KST.SConstruction
