module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiSOneCoreComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionBoundaryAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryFamilyEvaluation

/-! # 元の一次方向実現比較と全 native dg 入力族
概要：先頭 S₁ を消す元の実現比較は、全 native Kan 関手族と厳密に可換する。
方針：各多次数の元の core 比較の自然性を、同じ対角次数で評価する。
規約：元の比較・全高次入力を保持する。使われ方：同じ境界商と隣接 K 段の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の一次方向実現比較は、全 native dg 関手族の作用に厳密に自然である。 -/
lemma presentedPerfectDGOneDirectionComparison_action (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (oneDirectionRealizationComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ▷
        (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      presentedPerfectDGMultiRealizationAction A r C D =
    presentedPerfectDGOneDirectionAction A r C D ≫
      oneDirectionRealizationComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  have hn := congrArg (fun q => q.app n z)
    ((presentedPerfectDGMultiSOneCoreComparison A r (fun _ => n)).property C D)
  have ht := presentedPerfectDGMultiRealizationAction_app A r C D n
    ((oneDirectionRealizationComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n z.1) z.2
  have hs := presentedPerfectDGOneDirectionAction_app A r C D n z.1 z.2
  exact ht.trans (hn.trans
    (congrArg (fun x => (oneDirectionRealizationComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n x) hs.symm))

/-- 元の標的商射を後合成した一次方向比較も、全 native 入力族に厳密に自然。 -/
lemma presentedPerfectDGOneDirectionComparisonQuotient_action (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    ((oneDirectionRealizationComparison (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ≫
      boundaryReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))) ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      uncurry (presentedPerfectDGBoundaryReducedFamilyMap A r C D ≫
        PointedObject.basedHomι
          (boundaryReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A C)))
          (boundaryReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A D)))) =
    presentedPerfectDGOneDirectionAction A (r + 1) C D ≫
      oneDirectionRealizationComparison (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) ≫
      boundaryReductionQuotient r
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) := by
  let X := stableCategoryModel (presentedPerfectDGStableCategory A C)
  let Y := stableCategoryModel (presentedPerfectDGStableCategory A D)
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  have he := congrArg (fun a => a.app n ((boundaryReductionQuotient r X).app n
    ((oneDirectionRealizationComparison (r + 1) X).app n z.1), z.2))
    (presentedPerfectDGBoundaryReducedFamilyMap_evaluation A r C D)
  have hq := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGBoundaryReducedAction_quotient A r C D) n)
    ((oneDirectionRealizationComparison (r + 1) X).app n z.1, z.2)
  have hn := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionComparison_action A (r + 1) C D) n) z
  exact he.trans (hq.trans (congrArg (fun x => (boundaryReductionQuotient r Y).app n x) hn))

end SerrePositivity.KST.SConstruction
