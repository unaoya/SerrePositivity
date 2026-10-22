module
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinder
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderNaturality

/-! # 元の可換正方形による実写像円柱の作用
概要：元の射の可換正方形を、同じ元の押し出し写像円柱の射に送る。
方針：元の円柱端点の自然性と押し出しの普遍性を使い、両包含・射影を回収する。
規約：ここでは同じ通常射の回収を確保する。使われ方：全 Hom の写像円柱作用。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 元の可換正方形は、円柱側と標的側の同じ実作用で貼り付け条件を保つ。 -/
lemma pointedTensorMappingCylinderMap_condition
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorCylinderEndMap 0 X ≫
        (pointedTensorInterval.{u} ◁ a ≫ pointedTensorMappingCylinderCylinder g) =
      f ≫ (b ≫ pointedTensorMappingCylinderTarget g) := by
  rw [← Category.assoc, pointedTensorCylinderEnd_naturality 0 a, Category.assoc,
    pointedTensorMappingCylinder_condition g, ← Category.assoc, h, Category.assoc]

/-- 元の可換正方形の、同じ実写像円柱への作用。 -/
def pointedTensorMappingCylinderMap
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorMappingCylinder f ⟶ pointedTensorMappingCylinder g :=
  pushout.desc (pointedTensorInterval.{u} ◁ a ≫ pointedTensorMappingCylinderCylinder g)
    (b ≫ pointedTensorMappingCylinderTarget g)
    (pointedTensorMappingCylinderMap_condition f g a b h)

/-- 円柱側への制限は、同じ元の左 smash の作用。 -/
lemma pointedTensorMappingCylinderCylinder_map
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorMappingCylinderCylinder f ≫ pointedTensorMappingCylinderMap f g a b h =
      pointedTensorInterval.{u} ◁ a ≫ pointedTensorMappingCylinderCylinder g :=
  pushout.inl_desc _ _ _

/-- 標的側への制限は、同じ元の標的射の作用。 -/
lemma pointedTensorMappingCylinderTarget_map
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorMappingCylinderTarget f ≫ pointedTensorMappingCylinderMap f g a b h =
      b ≫ pointedTensorMappingCylinderTarget g :=
  pushout.inr_desc _ _ _

/-- 元の源比較も、同じ元の可換正方形の作用に自然。 -/
lemma pointedTensorMappingCylinderSource_map
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorMappingCylinderSource f ≫ pointedTensorMappingCylinderMap f g a b h =
      a ≫ pointedTensorMappingCylinderSource g := by
  change (pointedTensorCylinderEndMap 1 X ≫ pointedTensorMappingCylinderCylinder f) ≫ _ = _
  rw [Category.assoc, pointedTensorMappingCylinderCylinder_map f g a b h,
    ← Category.assoc, pointedTensorCylinderEnd_naturality 1 a, Category.assoc]
  rfl

/-- 同じ元の写像円柱射影も、元の可換正方形の作用に自然。 -/
lemma pointedTensorMappingCylinderMap_projection
    {X Y X' Y' : PointedSimplicialSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b) :
    pointedTensorMappingCylinderMap f g a b h ≫ pointedTensorMappingCylinderProjection g =
      pointedTensorMappingCylinderProjection f ≫ b := by
  apply pushout.hom_ext
  · change pointedTensorMappingCylinderCylinder f ≫ (_ ≫ _) =
      pointedTensorMappingCylinderCylinder f ≫ (_ ≫ _)
    rw [← Category.assoc, pointedTensorMappingCylinderCylinder_map f g a b h,
      Category.assoc, pointedTensorMappingCylinderCylinder_projection g, ← Category.assoc,
      pointedTensorCylinderProjection_naturality a, Category.assoc, h,
      ← Category.assoc (pointedTensorMappingCylinderCylinder f),
      pointedTensorMappingCylinderCylinder_projection f, Category.assoc]
  · change pointedTensorMappingCylinderTarget f ≫ (_ ≫ _) =
      pointedTensorMappingCylinderTarget f ≫ (_ ≫ _)
    rw [← Category.assoc, pointedTensorMappingCylinderTarget_map f g a b h,
      Category.assoc, pointedTensorMappingCylinderTarget_projection g,
      Category.comp_id, ← Category.assoc,
      pointedTensorMappingCylinderTarget_projection f, Category.id_comp]

end SerrePositivity.KST.SConstruction
