module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderAnodyne
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinder
public import SerrePositivity.KST.SConstruction.PointedMappingLocalizedImage

/-! # 同じ元の実写像円柱の射影の局所化可逆性
概要：同じ写像円柱の標的包含は anodyne で、元の射影は局所化で可逆。
方針：零端の anodyne 性を実押し出しへ移し、元の厳密な切断の等号を使う。
規約：元の射と入力に Kan 性を仮定しない。使われ方：BF 関手的単射置換の弱比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 同じ元の実写像円柱の標的包含は、基礎単体集合上で anodyne。 -/
lemma pointedTensorMappingCylinderTarget_anodyne
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    anodyneExtensions (pointedTensorMappingCylinderTarget f).right :=
  pointedPushout_inr_anodyne _ f (pointedTensorCylinderEndMap_anodyne 0 X)

/-- anodyne を反転する任意の関手は、同じ元の写像円柱射影を反転する。 -/
lemma pointedTensorMappingCylinderProjection_localized_isIso
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : anodyneExtensions.IsInvertedBy L)
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    IsIso (L.map (pointedTensorMappingCylinderProjection f).right) := by
  let _ : IsIso (L.map (pointedTensorMappingCylinderTarget f).right) :=
    hL _ (pointedTensorMappingCylinderTarget_anodyne f)
  have h := congrArg (fun q => L.map q.right)
    (pointedTensorMappingCylinderTarget_projection f)
  simp only [Under.comp_right, Under.id_right, L.map_comp, L.map_id] at h
  exact IsIso.of_isIso_fac_left h

/-- 元の射が局所化可逆なら、同じ実写像円柱への源比較も局所化可逆。 -/
lemma pointedTensorMappingCylinderSource_localized_isIso
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : anodyneExtensions.IsInvertedBy L)
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) [IsIso (L.map f.right)] :
    IsIso (L.map (pointedTensorMappingCylinderSource f).right) := by
  let _ := pointedTensorMappingCylinderProjection_localized_isIso L hL f
  have h := congrArg (fun q => L.map q.right)
    (pointedTensorMappingCylinderSource_projection f)
  simp only [Under.comp_right, L.map_comp] at h
  exact IsIso.of_isIso_fac_right h

end SerrePositivity.KST.SConstruction
