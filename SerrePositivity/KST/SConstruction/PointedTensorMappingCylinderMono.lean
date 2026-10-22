module
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinder
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderBoundaryMono
public import SerrePositivity.KST.SConstruction.CoproductPushoutAttachment
public import SerrePositivity.KST.SConstruction.PointedPushoutMonomorphism

/-! # 元の実写像円柱の源比較の単射性
概要：任意の元の点つき射に対し、同じ実写像円柱の源比較が基礎単射であることを示す。
方針：元の両端和を押し出した比較を単射にし、残った源の余積包含で制限する。
規約：入力射の単射性・Kan 性を仮定しない。使われ方：関手的 BF 単射置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 点つき余積の左包含は、同じ元の零射を使う基礎分裂単射。 -/
instance pointedCoprod_inl_isSplitMono (X Y : PointedSimplicialSet.{u}) :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y).right :=
  IsSplitMono.mk' ⟨(coprod.desc (𝟙 X) (0 : Y ⟶ X)).right,
    congrArg Under.Hom.right (coprod.inl_desc (𝟙 X) (0 : Y ⟶ X))⟩

/-- 点つき余積の右包含も、同じ元の零射を使う基礎分裂単射。 -/
instance pointedCoprod_inr_isSplitMono (X Y : PointedSimplicialSet.{u}) :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y).right :=
  IsSplitMono.mk' ⟨(coprod.desc (0 : X ⟶ Y) (𝟙 Y)).right,
    congrArg Under.Hom.right (coprod.inr_desc (0 : X ⟶ Y) (𝟙 Y))⟩

/-- 元の源比較と標的包含を束ねた、同じ実写像円柱への比較。 -/
def pointedTensorMappingCylinderPair {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    X ⨿ Y ⟶ pointedTensorMappingCylinder f :=
  coproductAttachmentComparison (pointedTensorCylinderEndMap 1 X)
    (pointedTensorCylinderEndMap 0 X) f

/-- 同じ実写像円柱は、元の両端和を貼り付けた実押し出しでもある。 -/
lemma pointedTensorMappingCylinderPair_isPushout {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    IsPushout
      (coprod.desc (pointedTensorCylinderEndMap 1 X) (pointedTensorCylinderEndMap 0 X))
      (coprod.map (𝟙 X) f) (pointedTensorMappingCylinderCylinder f)
      (pointedTensorMappingCylinderPair f) :=
  coproductAttachment_isPushout (pointedTensorCylinderEndMap 1 X)
    (pointedTensorCylinderEndMap 0 X) f

/-- 同じ実写像円柱への源・標的の和の比較は、基礎単射。 -/
instance pointedTensorMappingCylinderPair_mono {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    Mono (pointedTensorMappingCylinderPair f).right :=
  pointedIsPushout_mono_right (pointedTensorMappingCylinderPair_isPushout f)

/-- 元の写像円柱源比較は、同じ元の源の余積包含に因子化する。 -/
lemma pointedTensorMappingCylinderSource_factor {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedTensorMappingCylinderSource f =
      (coprod.inl : X ⟶ X ⨿ Y) ≫ pointedTensorMappingCylinderPair f := by
  rw [pointedTensorMappingCylinderPair, coproductAttachmentComparison]
  erw [coprod.inl_desc]
  rfl

/-- 任意の元の点つき射の同じ実写像円柱源比較は、追加仮定なしに基礎単射。 -/
instance pointedTensorMappingCylinderSource_mono {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    Mono (pointedTensorMappingCylinderSource f).right := by
  rw [pointedTensorMappingCylinderSource_factor]
  change Mono ((coprod.inl : X ⟶ X ⨿ Y).right ≫ (pointedTensorMappingCylinderPair f).right)
  infer_instance

/-- 同じ実写像円柱の元の標的包含も、追加仮定なしに基礎単射。 -/
instance pointedTensorMappingCylinderTarget_mono {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    Mono (pointedTensorMappingCylinderTarget f).right := by
  let _ : IsSplitMono (pointedTensorCylinderEndMap 0 X).right :=
    pointedTensorCylinderEnd_isSplitMono 0 ⟨X⟩
  exact pointedPushout_inr_mono (pointedTensorCylinderEndMap 0 X) f

end SerrePositivity.KST.SConstruction
