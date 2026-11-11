module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingAugmentedStages
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CofinalSimplexTowerGluing

/-!
概要：交互有限段列を、元の小さい添字の全可算図式と固定標的 slice 内の全可算図式へ貼り合わせる。
方針：添字では全段階、増大図式では共終な偶数段階の貼り合わせを使う。
規約：各有限段の全図式と全増大余錐を厳密に回収する。
使われ方：可算交互表示の cofinal 部分列とその余極限の比較。

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

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
  {B : SSet.{u + 1}} [Quasicategory B]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (hD : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
  (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex)

/-- 概要：元の小さい表示添字内に全可算図式を構成する。
方針：交互段の小さい前置図式を全段階で貼り合わせる。
規約：各段の全前置単体を厳密に回収する。
使われ方：compact 表示段の可算部分図式。 -/
lemma exists_alternatingPresentationIndexDiagram (i : I _⦋0⦌) :
    ∃ J : nerve (ULift.{u} ℕ) ⟶ I, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).index := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialDiagram_of_cofinalSimplices (fun n ↦ n) monotone_id
    (fun m ↦ ⟨m, le_refl m⟩)
  intro n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefix_succ]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower_index_front hμ D c hc hD hv i n

/-- 概要：元の固定標的の slice 内で全交互可算図式を構成する。
方針：全交互段の偶数前置面の整合を共終な段階の貼り合わせに渡す。
規約：増大余錐の全高次成分を同時に回収する。
使われ方：全可算図式の固定標的上の比較。 -/
lemma exists_alternatingPresentationSliceDiagram (i : I _⦋0⦌) :
    ∃ H : nerve (ULift.{u + 1} ℕ) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex), ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫ H =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialDiagram_of_cofinalSimplices (fun n ↦ 2 * n)
    (by intro n m h; change 2 * n ≤ 2 * m; omega)
    (fun m ↦ ⟨m, by change m ≤ 2 * m; omega⟩)
  intro n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationSuccessor.next_sliceDiagram_prefix
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n))

/-- 概要：全交互可算図式と元の標的への一つの全増大余錐を構成する。
方針：固定標的 slice 内の全図式を uncurry して、射影を底の図式に取る。
規約：元の標的頂点と各有限段の全余錐値を厳密に保つ。
使われ方：偶数・奇数の cofinal 部分列による余極限比較。 -/
lemma exists_alternatingPresentationAugmentedDiagram (i : I _⦋0⦌) :
    ∃ (F : nerve (ULift.{u + 1} ℕ) ⟶ B) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F),
      v.vertex = c.vertex ∧ ∀ n,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫ F =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).diagram ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n)) (𝟙 Δ[0]) ≫ v.val =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).augmentation.val := by
  obtain ⟨H, hH⟩ := exists_alternatingPresentationSliceDiagram hμ D c hc hD hv i
  let F := H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)
  let v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry H, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection H⟩
  refine ⟨F, v, ?_, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, Equiv.apply_symm_apply]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫
      (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c.vertex)) = _
    rw [← Category.assoc, hH n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage.sliceDiagram_projection]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n)) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry H = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, hH n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage.sliceDiagram_uncurry]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
