module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingEvenSubsequenceComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingOddSubsequenceComparison

/-!
概要：元の compact filtered 表示から、固定標的上の native な全交互可算図式と両部分列比較を構成する。
方針：全交互有限段を貼り合わせ、偶数部分は全射の等式、奇数部分は全関手同型で回収する。
規約：比較界面を追加入力にせず、元の表示余錐を使って構成する。
使われ方：固定標的 fiber の compact 頂点の可算回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の compact 表示から native な全交互図式と偶数・奇数の全比較を構成する。
方針：全小さい添字図式と固定標的 slice 図式を貼り合わせ、宇宙同型で native 添字へ移す。
規約：元の指定始端 i と全表示余錐を保持し、全 FunctorIso を返す。
使われ方：可算交互構成の条件付き比較入力を具体的な表示から供給する。 -/
lemma exists_nativeAlternatingPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {B : SSet.{u + 1}} [Quasicategory B]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ i : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) (i : I _⦋0⦌) :
    ∃ (J : nerve (ULift.{u} ℕ) ⟶ I)
      (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
        sliceOver (SSet.yonedaEquiv.symm c.vertex)),
      (∀ n, sequentialNerveInitialSimplex n ≫ J =
        (alternatingPresentationTower hμ D c hc hD hv i n).index) ∧
      (SSet.uliftFunctor.{u + 1, u}).map J ≫ coconeSliceDiagram c =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
          (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫ F ∧
      Nonempty (FunctorIso
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap
          (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ F)
        (SSet.const (sliceIdentityCone c.vertex))) := by
  obtain ⟨J, hJ⟩ := exists_alternatingPresentationIndexDiagram hμ D c hc hD hv i
  obtain ⟨H, hH⟩ := exists_alternatingPresentationSliceDiagram hμ D c hc hD hv i
  let F := sequentialNerveUniverseIso.hom ≫ H
  refine ⟨J, F, hJ, ?_, ?_⟩
  · exact alternatingPresentation_even_diagram_eq hμ D c hc hD hv i J hJ H hH
  · let e := (alternatingPresentation_oddSubsequenceIso hμ D c hc hD hv i H hH).precomp
      sequentialNerveUniverseIso.hom
    have he : sequentialNerveUniverseIso.hom ≫
        (nerveMap (sequentialSubsequenceFunctor.{u + 1} (fun n ↦ 2 * n + 1)
          alternatingOdd_monotone) ≫ H) =
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
          (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n + 1) alternatingOdd_monotone)) ≫ F := by
      rw [← Category.assoc, ← sequentialNerveUniverseIso_subsequence, Category.assoc]
    have ht : sequentialNerveUniverseIso.hom ≫ SSet.const (sliceIdentityCone c.vertex) =
        SSet.const (sliceIdentityCone c.vertex) := SSet.comp_const _ _
    rw [he, ht] at e
    exact ⟨e⟩

end SerrePositivity.InfinityCategories.F2.Presentable
