module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionComparisonAction
public import SerrePositivity.KST.SConstruction.CofiberFamilyComparison
public import SerrePositivity.KST.SConstruction.PointedFamilyPost

/-! # 元の一次方向境界商比較の全 native 入力族自然性
概要：元の S₁ 境界商比較は、同じ商上の全 native Kan 関手族と厳密に可換する。
方針：元の商射回収と実現比較の全族自然性を、同じ cofiber の検出へ渡す。
規約：逆射を選ばず全高次入力を保持する。使われ方：隣接 K 段と Kan 置換の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories Spectra
variable (A : Type u) [CommRing A]

/-- 元の商射の像で、源側の作用と比較の合成を降下前の同じ像で回収する。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_source_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).right.app n
      ((presentedPerfectDGOneDirectionReducedAction A r C D).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p)) =
    (boundaryReductionQuotient r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n
      ((oneDirectionRealizationComparison (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n
        ((presentedPerfectDGOneDirectionAction A (r + 1) C D).app n (x, p))) := by
  let Y := stableCategoryModel (presentedPerfectDGStableCategory A D)
  have hs := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionReducedAction_quotient A r C D) n) (x, p)
  have hg := types_congr_hom (NatTrans.congr_app
    (oneDirectionReducedComparison_quotient r Y) n)
    ((presentedPerfectDGOneDirectionAction A (r + 1) C D).app n (x, p))
  exact (congrArg (fun y => (oneDirectionReducedComparison r Y).right.app n y) hs).trans hg

/-- 元の商射の像で、標的側の比較と作用の合成を降下前の同じ像で回収する。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_target_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (presentedPerfectDGBoundaryReducedAction A r C D).app n
      ((oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right.app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x), p) =
    (boundaryReductionQuotient r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n
      ((oneDirectionRealizationComparison (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A D))).app n
        ((presentedPerfectDGOneDirectionAction A (r + 1) C D).app n (x, p))) := by
  let X := stableCategoryModel (presentedPerfectDGStableCategory A C)
  let Y := stableCategoryModel (presentedPerfectDGStableCategory A D)
  have hf := types_congr_hom (NatTrans.congr_app
    (oneDirectionReducedComparison_quotient r X) n) x
  have hq := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGBoundaryReducedAction_quotient A r C D) n)
    ((oneDirectionRealizationComparison (r + 1) X).app n x, p)
  have hn := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGOneDirectionComparison_action A (r + 1) C D) n) (x, p)
  exact (congrArg (fun y => (presentedPerfectDGBoundaryReducedAction A r C D).app n (y, p))
    hf).trans (hq.trans (congrArg (fun y => (boundaryReductionQuotient r Y).app n y) hn))

/-- 元の商射の各入力単体上で、元の境界商比較の全族自然性を回収する。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_quotient_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).right.app n
      ((presentedPerfectDGOneDirectionReducedAction A r C D).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p)) =
    (presentedPerfectDGBoundaryReducedAction A r C D).app n
      ((oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right.app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x), p) :=
  (presentedPerfectDGOneDirectionReducedComparison_source_app A r C D n x p).trans
    (presentedPerfectDGOneDirectionReducedComparison_target_app A r C D n x p).symm

/-- 源の同じ全 basedHom 族の評価は、元の商作用の後で同じ比較を施す。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_family_source_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).right.app n
      ((uncurry (presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
        PointedObject.basedHomι
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A C)))
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A D))))).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p)) =
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).right.app n
      ((presentedPerfectDGOneDirectionReducedAction A r C D).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p)) := by
  rw [presentedPerfectDGOneDirectionReducedFamilyMap_evaluation]

/-- 標的の同じ全 basedHom 族の評価は、元の商作用そのものを回収する。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_family_target_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (uncurry (presentedPerfectDGBoundaryReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D))))).app n
      ((oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right.app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x), p) =
    (presentedPerfectDGBoundaryReducedAction A r C D).app n
      ((oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right.app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x), p) := by
  rw [presentedPerfectDGBoundaryReducedFamilyMap_evaluation]

/-- 同じ商射の像では、元の全 basedHom 族の作用と比較が厳密に可換する。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_family_quotient_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor (r + 1)).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).right.app n
      ((uncurry (presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
        PointedObject.basedHomι
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A C)))
          (oneDirectionReducedRealization r
            (stableCategoryModel (presentedPerfectDGStableCategory A D))))).app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x, p)) =
    (uncurry (presentedPerfectDGBoundaryReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D))))).app n
      ((oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right.app n
        ((oneDirectionReductionQuotient r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).app n x), p) :=
  (presentedPerfectDGOneDirectionReducedComparison_family_source_app A r C D n x p).trans
    ((presentedPerfectDGOneDirectionReducedComparison_quotient_app A r C D n x p).trans
      (presentedPerfectDGOneDirectionReducedComparison_family_target_app A r C D n x p).symm)

/-- 元の商比較と全入力族を先に固定した、全単体自然性の検出。 -/
def presentedPerfectDGOneDirectionReducedComparisonBuilder (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :=
  cofiberFamily_comparison_of_app (P := C ⟶[SSet.{max (u + 1) v}] D)
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C))).ι
    (boundaryReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)))
    (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D)))
    (boundaryReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D)))
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)))
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D)))
    (presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D)
    (presentedPerfectDGBoundaryReducedFamilyMap.{u, v} A r C D)

/-- 元の一次方向境界商比較は、同じ元の全基点固定写像族に厳密に自然である。 -/
lemma presentedPerfectDGOneDirectionReducedComparison_family (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D ≫
      pointedFamilyPost
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D)))
        (oneDirectionReducedComparison r
          (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D))) =
    presentedPerfectDGBoundaryReducedFamilyMap.{u, v} A r C D ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (oneDirectionReducedComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A D))) := by
  exact presentedPerfectDGOneDirectionReducedComparisonBuilder.{u, v} A r C D
    (presentedPerfectDGOneDirectionReducedComparison_family_quotient_app A r C D)

end SerrePositivity.KST.SConstruction
