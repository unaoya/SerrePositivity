module
public import SerrePositivity.KST.SConstruction.StableZeroBoundaryAction
public import SerrePositivity.KST.SConstruction.CofiberFamilyActionLaws

/-! # 元の全零境界商への完全関手の全作用
概要：元の実現作用を同じ全零境界商へ降ろし、全パラメータで基点を厳密に保つ。
方針：既存の商の実際の pushout と basedHom への普遍的降下を使う。
規約：元の商・商射・基点を変更しない。使われ方：点つき Kan 置換と豊穣 BF K。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants Spectra

/-- 元の全零境界は、標的の同じ商の基点へ全パラメータで厳密に送られる。 -/
lemma stableBoundaryReducedAction_collapse (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel C)).ι ▷
        (C ⟶[SSet.{u}] D)) ≫
      stableMultiRealizationAction (r + 1) C D ≫
        boundaryReductionQuotient r
          (stableCategoryModel D) =
      toUnit _ ≫ (boundaryReducedRealization r
        (stableCategoryModel D)).hom :=
  boundaryFamily_collapse _ _ _ (stableZeroBoundaryAction (r + 1) C D)
    (stableZeroBoundaryAction_inclusion (r + 1) C D)

/-- 同じ元の全零境界商への、完全関手の全自然同値入力族による実作用。 -/
def stableBoundaryReducedAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (boundaryReducedRealization r
      (stableCategoryModel C)).right ⊗
        (C ⟶[SSet.{u}] D) ⟶
      (boundaryReducedRealization r
        (stableCategoryModel D)).right :=
  cofiberFamilyDescRaw
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel C)).ι
    (boundaryReducedRealization r
      (stableCategoryModel D))
    (stableMultiRealizationAction (r + 1) C D ≫
      boundaryReductionQuotient r (stableCategoryModel D))
    (stableBoundaryReducedAction_collapse r C D)

/-- 同じ元の商射に沿って、同じ完全関手の全実現作用を厳密に回収する。 -/
lemma stableBoundaryReducedAction_quotient (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (boundaryReductionQuotient r
      (stableCategoryModel C) ▷
        (C ⟶[SSet.{u}] D)) ≫ stableBoundaryReducedAction r C D =
      stableMultiRealizationAction (r + 1) C D ≫
        boundaryReductionQuotient r
          (stableCategoryModel D) :=
  cofiberFamilyDescRaw_quotient _ _ _ _

/-- 完全関手の全入力族は、同じ元の商の基点を全パラメータで厳密に保つ。 -/
lemma stableBoundaryReducedAction_basepoint (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((boundaryReducedRealization r
      (stableCategoryModel C)).hom ▷
        (C ⟶[SSet.{u}] D)) ≫ stableBoundaryReducedAction r C D =
      toUnit _ ≫ (boundaryReducedRealization r
        (stableCategoryModel D)).hom :=
  cofiberFamilyDescRaw_basepoint _ _ _ _

/-- 同じ元の境界商の、全パラメータを保持する実基点固定写像族。 -/
def stableBoundaryReducedFamilyMap (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (C ⟶[SSet.{u}] D) ⟶
      (PointedObject.basedHom
        (boundaryReducedRealization r
          (stableCategoryModel C))
        (boundaryReducedRealization r
          (stableCategoryModel D))).right :=
  cofiberFamilyDesc
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel C)).ι
    (boundaryReducedRealization r
      (stableCategoryModel D))
    (stableMultiRealizationAction (r + 1) C D ≫
      boundaryReductionQuotient r (stableCategoryModel D))
    (stableBoundaryReducedAction_collapse r C D)

/-- 基点固定写像族の包含後には、同じ元の商作用の curry を回収する。 -/
lemma stableBoundaryReducedFamilyMap_inclusion (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableBoundaryReducedFamilyMap r C D ≫
      PointedObject.basedHomι
        (boundaryReducedRealization r
          (stableCategoryModel C))
        (boundaryReducedRealization r
          (stableCategoryModel D)) =
      curry (stableBoundaryReducedAction r C D) :=
  Limits.equalizer.lift_ι _ _

end SerrePositivity.KST.SConstruction
