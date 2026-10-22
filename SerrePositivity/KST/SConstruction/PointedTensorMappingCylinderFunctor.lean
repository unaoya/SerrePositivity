module
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderMap
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # 元の射と可換正方形を保つ実写像円柱関手
概要：同じ押し出しへの作用が恒等・合成を保つことを示し、元の射圏の関手に束ねる。
方針：円柱側と標的側の両包含で等号を検出する。
規約：これは通常関手で、全 Hom の豊穣性は別途接続する。使われ方：関手的 BF 置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 恒等正方形は、元の同じ実写像円柱の恒等射に移る。 -/
lemma pointedTensorMappingCylinderMap_id {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (h : 𝟙 X ≫ f = f ≫ 𝟙 Y) :
    pointedTensorMappingCylinderMap f f (𝟙 X) (𝟙 Y) h = 𝟙 _ := by
  apply pushout.hom_ext
  · change pointedTensorMappingCylinderCylinder f ≫ _ =
      pointedTensorMappingCylinderCylinder f ≫ _
    rw [pointedTensorMappingCylinderCylinder_map f f (𝟙 X) (𝟙 Y) h, whiskerLeft_id,
      Category.id_comp,
      Category.comp_id]
  · change pointedTensorMappingCylinderTarget f ≫ _ =
      pointedTensorMappingCylinderTarget f ≫ _
    rw [pointedTensorMappingCylinderTarget_map f f (𝟙 X) (𝟙 Y) h,
      Category.id_comp, Category.comp_id]

/-- 元の可換正方形の二回作用は、同じ合成正方形の作用に厳密に一致する。 -/
lemma pointedTensorMappingCylinderMap_comp
    {X Y X' Y' X'' Y'' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : X'' ⟶ Y'')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ g = f ≫ b)
    (c : X' ⟶ X'') (d : Y' ⟶ Y'') (j : c ≫ k = g ≫ d)
    (l : (a ≫ c) ≫ k = f ≫ (b ≫ d)) :
    pointedTensorMappingCylinderMap f g a b h ≫ pointedTensorMappingCylinderMap g k c d j =
      pointedTensorMappingCylinderMap f k (a ≫ c) (b ≫ d) l := by
  apply pushout.hom_ext
  · change pointedTensorMappingCylinderCylinder f ≫ (_ ≫ _) =
      pointedTensorMappingCylinderCylinder f ≫ _
    rw [← Category.assoc, pointedTensorMappingCylinderCylinder_map f g a b h, Category.assoc,
      pointedTensorMappingCylinderCylinder_map g k c d j,
      pointedTensorMappingCylinderCylinder_map f k (a ≫ c) (b ≫ d) l,
      whiskerLeft_comp, Category.assoc]
  · change pointedTensorMappingCylinderTarget f ≫ (_ ≫ _) =
      pointedTensorMappingCylinderTarget f ≫ _
    rw [← Category.assoc, pointedTensorMappingCylinderTarget_map f g a b h, Category.assoc,
      pointedTensorMappingCylinderTarget_map g k c d j,
      pointedTensorMappingCylinderTarget_map f k (a ≫ c) (b ≫ d) l,
      Category.assoc]

/-- 元の全点つき射と可換正方形から、同じ実写像円柱への通常関手。 -/
def pointedTensorMappingCylinderFunctor :
    Arrow PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u} where
  obj f := pointedTensorMappingCylinder f.hom
  map {f g} s := pointedTensorMappingCylinderMap f.hom g.hom s.left s.right s.w
  map_id f := pointedTensorMappingCylinderMap_id f.hom _
  map_comp {f g k} s t :=
    (pointedTensorMappingCylinderMap_comp f.hom g.hom k.hom s.left s.right s.w
      t.left t.right t.w _).symm

end SerrePositivity.KST.SConstruction
