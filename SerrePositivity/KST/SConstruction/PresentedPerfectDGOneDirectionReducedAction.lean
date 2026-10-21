module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionBoundaryAction
public import SerrePositivity.KST.SConstruction.CofiberFamilyActionLaws

/-! # 元の一次方向の全零境界商への全 native dg 作用
概要：元の一次方向実現作用を同じ全零境界商へ降ろし、全パラメータで基点を厳密に保つ。
方針：既存の商の実際の pushout と basedHom への普遍的降下を使う。
規約：元の商・商射・基点を変更しない。使われ方：点つき Kan 置換と豊穣 BF K。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories Spectra
variable (A : Type u) [CommRing A]

/-- 元の一次方向の全零境界は、標的の同じ商の基点へ全パラメータで厳密に送られる。 -/
lemma presentedPerfectDGOneDirectionReducedAction_collapse (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    ((oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι ▷
        (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
        oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)) =
      toUnit _ ≫ (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).hom :=
  boundaryFamily_collapse _ _ _ (presentedPerfectDGOneDirectionBoundaryAction A (r + 1) C D)
    (presentedPerfectDGOneDirectionBoundaryAction_inclusion A (r + 1) C D)

/-- 同じ元の一次方向の全零境界商への、全 native Kan dg 入力族による実作用。 -/
def presentedPerfectDGOneDirectionReducedAction (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right ⊗
        (C ⟶[SSet.{max (u + 1) v}] D) ⟶
      (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).right :=
  cofiberFamilyDescRaw
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι
    (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A D)))
    (presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
      oneDirectionReductionQuotient r (stableCategoryModel (presentedPerfectDGStableCategory A D)))
    (presentedPerfectDGOneDirectionReducedAction_collapse A r C D)

/-- 同じ元の商射に沿って、同じ全 native 実現作用を厳密に回収する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_quotient (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (oneDirectionReductionQuotient r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ▷
        (C ⟶[SSet.{max (u + 1) v}] D)) ≫ presentedPerfectDGOneDirectionReducedAction A r C D =
      presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
        oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)) :=
  cofiberFamilyDescRaw_quotient _ _ _ _

/-- 全 native 入力族は、同じ元の商の基点を全パラメータで厳密に保つ。 -/
lemma presentedPerfectDGOneDirectionReducedAction_basepoint (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    ((oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).hom ▷
        (C ⟶[SSet.{max (u + 1) v}] D)) ≫ presentedPerfectDGOneDirectionReducedAction A r C D =
      toUnit _ ≫ (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).hom :=
  cofiberFamilyDescRaw_basepoint _ _ _ _

/-- 同じ元の境界商の、全パラメータを保持する実基点固定写像族。 -/
def presentedPerfectDGOneDirectionReducedFamilyMap (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (C ⟶[SSet.{max (u + 1) v}] D) ⟶
      (PointedObject.basedHom
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)))).right :=
  cofiberFamilyDesc
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι
    (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A D)))
    (presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
      oneDirectionReductionQuotient r (stableCategoryModel (presentedPerfectDGStableCategory A D)))
    (presentedPerfectDGOneDirectionReducedAction_collapse A r C D)

/-- 基点固定写像族の包含後には、同じ元の商作用の curry を回収する。 -/
lemma presentedPerfectDGOneDirectionReducedFamilyMap_inclusion (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D))) =
      curry (presentedPerfectDGOneDirectionReducedAction A r C D) :=
  Limits.equalizer.lift_ι _ _

end SerrePositivity.KST.SConstruction
