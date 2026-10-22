module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.SOAExInfinityAdjointComparison

/-! # 同じ単位上の回収による旧・新組み立て随伴の比較
概要：元の SOA 随伴延長と新 Ex∞ 右脚の随伴は前向き比較で点つき成分が一致する。
方針：二つの射を同じ anodyne 源単位からの厳密延長として比較する。
規約：入力ごとの弱比較にだけ延長を使う。使われ方：正の BF 構造射の比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の一次方向商の SOA Kan 模型から同じ Ex∞ 模型への前向き比較。 -/
def presentedPerfectDGBFSourceSOAComparison (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (oneDirectionKanRealizationFunctor r).obj
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶
      ((presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C).obj :=
  pointedSOAExInfinityComparison ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)

/-- 元の随伴の SOA 延長と新 Ex∞ 随伴は、同じ前向き比較で点つき成分が可換。 -/
lemma presentedPerfectDGBFSOAAssemblyAdjoint_component (r : ℕ)
    (C : PerfDGInput.{u, v} A)
    (w : (kanAssemblyAdjointChoices r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))) _⦋0⦌) :
    componentOf (presentedPerfectDGBFSourceSOAComparison A r C ≫
        presentedPerfectDGKanAssemblyRightAdjoint A r C) =
      componentOf (kanAssemblyAdjointAt r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)) w ≫
        (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map
          (presentedPerfectDGBFBoundarySOAComparison A (r + 1) C)) := by
  apply soaExInfinityAdjoint_component
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
    ((presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).obj C)
    ((oneDirectionAssemblyAdjointNat r).app
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))
  · exact kanAssemblyAdjointAt_fac r _ w
  · exact presentedPerfectDGKanAssemblyRightAdjoint_unit A r C

end SerrePositivity.KST.SConstruction
