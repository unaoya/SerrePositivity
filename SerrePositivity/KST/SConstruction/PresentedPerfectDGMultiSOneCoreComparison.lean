module
public import SerrePositivity.KST.SConstruction.MultiSOneEnrichedComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiSCoreDiagram

/-! # 元の反復 S₁ 比較を保つ全 native core 比較
概要：元の反復の先頭 S₁ 比較と、その全高次自然性を実 dg 入力の core に移す。
方針：実 Perf 豊穣関手で前合成し、同じ対象 core の関手を適用する。
規約：全入力 Hom は非離散のまま保持する。使われ方：一次方向の実現・境界商比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 全 native dg 入力族に自然な、元の反復 core S₁ 比較そのもの。 -/
def presentedPerfectDGMultiSOneCoreComparison (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedComparison
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)).obj
        ((oneDirectionIndex r).obj d))
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj d) :=
  quasicategoryEnrichedObjectCoreFunctor.map
    ((multiSOneQuasicategoryEnrichedComparison r d).precompose
      (presentedPerfectDGFullEnrichedFunctor A))

/-- 比較成分は、同じ元の反復 core S₁ 比較の成分を厳密に回収する。 -/
lemma presentedPerfectDGMultiSOneCoreComparison_val (r : ℕ)
    (d : Fin r → SimplexCategoryᵒᵖ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGMultiSOneCoreComparison A r d).val C =
      (multiCoreSOneComparison r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).app d := rfl

end SerrePositivity.KST.SConstruction
