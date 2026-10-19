module
public import SerrePositivity.KST.SConstruction.SOneSlideComparison
public import SerrePositivity.KST.SConstruction.SubcomplexCofiberIso
public import SerrePositivity.KST.SConstruction.MultiSOneSlideCore
public import SerrePositivity.KST.SConstruction.CoordinateZeroIso
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison

/-! # 元の S₁ 内外交換による源の全零境界の保存
概要：入力 S₁ の反復の全零境界を、元の最外側 S₁ の残りの全零境界へ厳密に写す。
方針：全多次数 core の自然同型と一般の零境界保存を用いる。
規約：既存の二つの境界部分複体を比較する。使われ方：構造射の源の商への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 元の S₁ 内外実現同型は、源の既存の全零境界を厳密に対応させる。 -/
lemma sOneInnerOuterRealizationIso_fatBoundary (r : ℕ) (X : StableModel.{u}) :
    (zeroDirectionsFatBoundary r (sStableModel 1 X)).image
      (sOneInnerOuterRealizationIso r X).hom = oneDirectionFatBoundary r X := by
  have h := coordinateZeroBoundary_image_iso Finset.univ ∅ (multiSOneSlideCoreIso r X)
  rw [multiSOneSlideCoreIso_realization] at h
  rw [oneDirectionFatBoundary_eq_coordinate]
  exact h

/-- 元の S₁ 内外交換による、構造射の源の既存の全零境界商の同型。 -/
def sOneInnerOuterReducedIso (r : ℕ) (X : StableModel.{u}) :
    boundaryReducedRealization r (sStableModel 1 X) ≅ oneDirectionReducedRealization r X :=
  subcomplexCofiberIso (zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X))
    (oneDirectionFatBoundary (r + 1) X) (sOneInnerOuterRealizationIso (r + 1) X)
    (sOneInnerOuterRealizationIso_fatBoundary (r + 1) X)

/-- 境界商の元の交換同型を商射へ引き戻すと、元の S₁ 実現交換を回収する。 -/
lemma sOneInnerOuterReducedIso_quotient (r : ℕ) (X : StableModel.{u}) :
    boundaryReductionQuotient r (sStableModel 1 X) ≫ (sOneInnerOuterReducedIso r X).hom.right =
      (sOneInnerOuterRealizationIso (r + 1) X).hom ≫ oneDirectionReductionQuotient r X :=
  subcomplexCofiberMap_quotient _ _ _
    (sOneInnerOuterRealizationIso_fatBoundary (r + 1) X).le

/-- 商へ降ろした S₁ 内外交換も、元の二つの前段比較と厳密に可換。 -/
lemma sOneInnerOuterReducedIso_comparison (r : ℕ) (X : StableModel.{u}) :
    (sOneInnerOuterReducedIso r X).hom ≫ oneDirectionReducedComparison r X =
      boundaryReducedRealizationMap r (stableSOneComparison X) := by
  apply PointedObject.cofiber_hom_ext
    (zeroDirectionsFatBoundary (r + 1) (sStableModel 1 X)).ι
  change boundaryReductionQuotient r (sStableModel 1 X) ≫
    ((sOneInnerOuterReducedIso r X).hom.right ≫ (oneDirectionReducedComparison r X).right) =
      boundaryReductionQuotient r (sStableModel 1 X) ≫
        (boundaryReducedRealizationMap r (stableSOneComparison X)).right
  rw [← Category.assoc, sOneInnerOuterReducedIso_quotient, Category.assoc,
    oneDirectionReducedComparison_quotient, ← Category.assoc,
    sOneInnerOuterRealizationIso_comparison, boundaryReducedRealizationMap_quotient]

end SerrePositivity.KST.SConstruction
