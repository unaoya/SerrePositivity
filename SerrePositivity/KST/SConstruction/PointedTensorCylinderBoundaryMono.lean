module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderBoundary

/-! # 同じ元の円柱の二端点の和の単射性
概要：時刻一・時刻零の同じ端点の余積射が基礎単体集合で単射であることを示す。
方針：境界の実余積表示からの同型と、元の境界の右 smash の単射を合成する。
規約：同じ元の二端点を保持する。使われ方：実写像円柱の源比較の単射性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open Spectra

/-- 二つの同じ X の余積から、同じ自由点つき境界の右 smash への実同型。 -/
def pointedTensorBoundaryCoproductIso (X : PointedSimplicialSet.{u}) :
    X ⨿ X ≅ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} ⊗ X :=
  (coprodIsCoprod X X).coconePointUniqueUpToIso (pointedTensorBoundaryIsColimit X)

/-- 元の時刻一側の包含は、同じ境界の端点成分を回収する。 -/
lemma pointedTensorBoundaryCoproductIso_inl (X : PointedSimplicialSet.{u}) :
    (coprod.inl : X ⟶ X ⨿ X) ≫ (pointedTensorBoundaryCoproductIso X).hom =
      (λ_ X).inv ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd.{u} ▷ X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X X)
    (pointedTensorBoundaryIsColimit X) ⟨WalkingPair.left⟩

/-- 元の時刻零側の包含は、同じ境界の端点成分を回収する。 -/
lemma pointedTensorBoundaryCoproductIso_inr (X : PointedSimplicialSet.{u}) :
    (coprod.inr : X ⟶ X ⨿ X) ≫ (pointedTensorBoundaryCoproductIso X).hom =
      (λ_ X).inv ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart.{u} ▷ X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod X X)
    (pointedTensorBoundaryIsColimit X) ⟨WalkingPair.right⟩

/-- 元の同じ円柱二端点の和は、境界同型と元の境界包含で厳密に因子化する。 -/
lemma pointedTensorCylinderBoundary_factor (X : PointedSimplicialSet.{u}) :
    coprod.desc (pointedTensorCylinderEndMap 1 X) (pointedTensorCylinderEndMap 0 X) =
      (pointedTensorBoundaryCoproductIso X).hom ≫ pointedTensorBoundaryInclusion.{u} ▷ X := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc, ← Category.assoc, pointedTensorBoundaryCoproductIso_inl,
      Category.assoc, ← comp_whiskerRight, pointedTensorBoundaryEnd_inclusion]
    rfl
  · rw [coprod.inr_desc, ← Category.assoc, pointedTensorBoundaryCoproductIso_inr,
      Category.assoc, ← comp_whiskerRight, pointedTensorBoundaryStart_inclusion]
    rfl

/-- 同じ元の円柱の二端点の和は、基礎単体集合上で単射。 -/
instance pointedTensorCylinderBoundary_mono (X : PointedSimplicialSet.{u}) :
    Mono (coprod.desc (pointedTensorCylinderEndMap 1 X)
      (pointedTensorCylinderEndMap 0 X)).right := by
  rw [pointedTensorCylinderBoundary_factor]
  change Mono ((pointedTensorBoundaryCoproductIso X).hom.right ≫
    (pointedTensorBoundaryInclusion.{u} ▷ X).right)
  let i : X ⨿ X ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeIntervalBoundary.{u} ⊗ X := (pointedTensorBoundaryCoproductIso X).hom
  let _ : IsSplitMono i.right := IsSplitMono.mk'
    ⟨(pointedTensorBoundaryCoproductIso X).inv.right,
      congrArg Under.Hom.right (pointedTensorBoundaryCoproductIso X).hom_inv_id⟩
  let _ : Mono (pointedTensorBoundaryInclusion.{u} ▷ X).right := pointedTensorBoundaryTensor_mono X
  change Mono (i.right ≫ (pointedTensorBoundaryInclusion.{u} ▷ X).right)
  infer_instance

end SerrePositivity.KST.SConstruction
