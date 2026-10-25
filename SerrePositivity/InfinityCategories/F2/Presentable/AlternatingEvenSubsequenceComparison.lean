module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingPresentationDiagrams
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialEvenFaceComparison

/-!
概要：全交互可算図式の偶数部分列を元の native 表示図式と全射の等式で比較する。
方針：全有限始区間で検出し、元の全増大余錐の偶数制限を使う。
規約：固定標的 slice 内の全射の厳密な等式。
使われ方：可算交互構成の第一成分と共通の基底図式の比較。
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

/-- 概要：元の小さい表示添字の全可算図式は、全交互図式の偶数部分列に厳密に一致する。
方針：native 全有限段で、同じ元の表示前置図式と増大余錐へ制限して検出する。
規約：固定標的 slice 内の全図式の等式。
使われ方：偶数部分列の colimit 比較に追加の高次整合入力を残さない。 -/
lemma alternatingPresentation_even_diagram_eq
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    {B : SSet.{u + 1}} [Quasicategory B]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ i : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) (i : I _⦋0⦌)
    (J : nerve (ULift.{u} ℕ) ⟶ I)
    (hJ : ∀ n, sequentialNerveInitialSimplex n ≫ J =
      (alternatingPresentationTower hμ D c hc hD hv i n).index)
    (H : nerve (ULift.{u + 1} ℕ) ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex))
    (hH : ∀ n, sequentialNerveInitialSimplex (2 * n) ≫ H =
      (alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram) :
    (SSet.uliftFunctor.{u + 1, u}).map J ≫ coconeSliceDiagram c =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) ≫
          sequentialNerveUniverseIso.hom ≫ H := by
  apply nativeSequential_hom_ext
  intro n
  calc
    _ = finiteStageBaseMap (alternatingPresentationTower hμ D c hc hD hv i n).index ≫
        coconeSliceDiagram c := by
      rw [← Category.assoc, nativeSequentialInitialSimplex_liftedDiagram, hJ n]
    _ = SSet.stdSimplex.map (sequentialEvenFace n) ≫
        (alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram :=
      (AlternatingPresentationStage.even_sliceDiagram _).symm
    _ = SSet.stdSimplex.map (sequentialEvenFace n) ≫
        sequentialNerveInitialSimplex (2 * n) ≫ H := by rw [hH n]
    _ = (nativeSequentialInitialSimplex n ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
          (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone))) ≫
        sequentialNerveUniverseIso.hom ≫ H := by
      rw [nativeSequentialInitialSimplex_even, Category.assoc,
        ← Category.assoc (nativeSequentialInitialSimplex (2 * n)) sequentialNerveUniverseIso.hom H,
        nativeSequentialInitialSimplex_universe]
    _ = _ := by simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
