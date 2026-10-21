module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryReducedAction

/-! # 元の二つの境界商の全写像族の評価
概要：basedHom に降ろした全入力族を評価すると、元の商上の作用を厳密に回収する。
方針：包含後の curry の式を uncurry する。
規約：元の同じ商を使う。使われ方：全パラメータの suspension 組み立て比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向の商の全写像族は、同じ元の商作用として評価される。 -/
lemma presentedPerfectDGOneDirectionReducedFamilyMap_evaluation (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    uncurry (presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)))) =
      presentedPerfectDGOneDirectionReducedAction A r C D :=
  (congrArg (uncurry (C := SSet.{max (u + 1) v}))
    (presentedPerfectDGOneDirectionReducedFamilyMap_inclusion A r C D)).trans (uncurry_curry _)

/-- 全方向の商の全写像族は、同じ元の商作用として評価される。 -/
lemma presentedPerfectDGBoundaryReducedFamilyMap_evaluation (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    uncurry (presentedPerfectDGBoundaryReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D)))) =
      presentedPerfectDGBoundaryReducedAction A r C D :=
  (congrArg (uncurry (C := SSet.{max (u + 1) v}))
    (presentedPerfectDGBoundaryReducedFamilyMap_inclusion A r C D)).trans (uncurry_curry _)

/-- 元の一次方向の商射に沿う全写像族は、降下前の同じ全作用を回収する。 -/
lemma presentedPerfectDGOneDirectionReducedFamilyMap_quotient (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (oneDirectionReductionQuotient r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ▷
        (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      uncurry (presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
        PointedObject.basedHomι
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A C)))
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A D)))) =
    presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
      oneDirectionReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) :=
  (congrArg (fun q => (oneDirectionReductionQuotient r
    (stableCategoryModel (presentedPerfectDGStableCategory A C)) ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫ q)
    (presentedPerfectDGOneDirectionReducedFamilyMap_evaluation A r C D)).trans
      (presentedPerfectDGOneDirectionReducedAction_quotient A r C D)

end SerrePositivity.KST.SConstruction
