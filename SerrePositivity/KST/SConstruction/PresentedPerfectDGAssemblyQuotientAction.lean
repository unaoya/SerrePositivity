module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryFamilyEvaluation
public import SerrePositivity.KST.SConstruction.ParameterizedQuotientSquare

/-! # 元の標的境界商への区間組み立ての全族自然性
概要：標的の同じ商射を区間組み立ての後へ合成しても、全族自然性を保つ。
方針：全族の商射回収と元の区間組み立ての可換式を合成する。
規約：検証上限を変えずに元の作用を照合する。使われ方：suspension への厳密降下。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 標的の元の商を取った区間組み立ても、全 native 入力族に厳密に自然である。 -/
lemma presentedPerfectDGAssemblyQuotient_action (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    ((multiDiagonalAssembly (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C)) ≫
      boundaryReductionQuotient (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A C))) ▷
      (C ⟶[SSet.{max (u + 1) v}] D)) ≫
      uncurry (presentedPerfectDGBoundaryReducedFamilyMap A (r + 1) C D ≫
        PointedObject.basedHomι
          (boundaryReducedRealization (r + 1)
            (stableCategoryModel (presentedPerfectDGStableCategory A C)))
          (boundaryReducedRealization (r + 1)
            (stableCategoryModel (presentedPerfectDGStableCategory A D)))) =
    (α_ (Δ[1] : SSet.{max (u + 1) v})
      ((oneDirectionRealizationFunctor (r + 1)).obj
        (stableCategoryModel (presentedPerfectDGStableCategory A C)))
      (C ⟶[SSet.{max (u + 1) v}] D)).hom ≫
      ((Δ[1] : SSet.{max (u + 1) v}) ◁ presentedPerfectDGOneDirectionAction A (r + 1) C D) ≫
      multiDiagonalAssembly (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) ≫
      boundaryReductionQuotient (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A D)) := by
  let X := stableCategoryModel (presentedPerfectDGStableCategory A C)
  let Y := stableCategoryModel (presentedPerfectDGStableCategory A D)
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  have he := congrArg (fun a => a.app n
    ((boundaryReductionQuotient (r + 1) X).app n
      ((multiDiagonalAssembly (r + 1) X).app n z.1), z.2))
    (presentedPerfectDGBoundaryReducedFamilyMap_evaluation A (r + 1) C D)
  have hq := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGBoundaryReducedAction_quotient A (r + 1) C D) n)
      ((multiDiagonalAssembly (r + 1) X).app n z.1, z.2)
  have hn := types_congr_hom (NatTrans.congr_app
    (presentedPerfectDGMultiDiagonalAssembly_action A (r + 1) C D) n) z
  exact he.trans (hq.trans
    (congrArg (fun x => (boundaryReductionQuotient (r + 1) Y).app n x) hn))

end SerrePositivity.KST.SConstruction
