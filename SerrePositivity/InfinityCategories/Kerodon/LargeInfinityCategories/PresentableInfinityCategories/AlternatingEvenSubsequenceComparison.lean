module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeSliceDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialEvenFaceComparison

/-!
概要：全交互可算図式の偶数部分列を元の native 表示図式と全射の等式で比較する。
方針：全有限始区間で検出し、元の全増大余錐の偶数制限を使う。
規約：固定標的 slice 内の全射の厳密な等式。
使われ方：可算交互構成の第一成分と共通の基底図式の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の小さい表示添字の全可算図式は、全交互図式の偶数部分列に厳密に一致する。
方針：native 全有限段で、同じ元の表示前置図式と増大余錐へ制限して検出する。
規約：固定標的 slice 内の全図式の等式。
使われ方：偶数部分列の colimit 比較に追加の高次整合入力を残さない。 -/
lemma alternatingPresentation_even_diagram_eq
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    {B : SSet.{u + 1}} [Quasicategory B]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hD : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) (i : I _⦋0⦌)
    (J : nerve (ULift.{u} ℕ) ⟶ I)
    (hJ : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).index)
    (H : nerve (ULift.{u + 1} ℕ) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex))
    (hH : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫ H =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram) :
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveUniverseIso.hom ≫ H := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequential_hom_ext
  intro n
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).index ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex_liftedDiagram, hJ n]
    _ = SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage.even_sliceDiagram _).symm
    _ = SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫ H := by rw [hH n]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex n ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingEven_monotone))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveUniverseIso.hom ≫ H := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex_even, Category.assoc,
        ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex (2 * n)) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveUniverseIso.hom H,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeSequentialInitialSimplex_universe]
    _ = _ := by simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
