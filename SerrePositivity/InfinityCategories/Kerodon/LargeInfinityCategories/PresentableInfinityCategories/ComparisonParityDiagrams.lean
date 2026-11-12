module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonParityShapes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSequenceSliceDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallShapeTowerGluing

/-!
概要：偶数・奇数面と同じ形状表示で、元の両添字図式と共通大域頂点上の全図式を貼り合わせる。
方針：同じ再帰的な三つの形状同型を、それぞれの公開貼合入口へ渡す。
規約：全有限段の厳密な回収式を同じ同型で保持する。使われ方：部分列の全比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] {C : SSet.{u + 1}} [Quasicategory C]
  {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
variable (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
  [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
  (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)

/-- 偶数・奇数面と同じ全形状同型で構成した、元の共通大域頂点上の全図式。 -/
lemma exists_comparisonParitySliceDiagram (e₀ : s₀.shape ≅ (Δ[1] : SSet.{u})) :
    ∃ H : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c₀.vertex), ∀ n,
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n + 1)) ≫ H =
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_nativeDiagram_of_shapeTower (fun n ↦ 2 * n + 1)
    (fun _ _ h ↦ Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1)
    (fun k ↦ ⟨k, by change k ≤ 2 * k + 1; omega⟩)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).simplexShapeIso_prefix hD₁
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n))
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceSliceDiagram_restrict hμ hC hc₀ hc₁ hD₀ hD₁ s₀)

/-- 偶数面と同じ左形状表示で、元の左添字圏内の全図式を構成する。 -/
lemma exists_comparisonLeftParityIndexDiagram (l₀ : s₀.left_shape ≅ (Δ[0] : SSet.{u})) :
    ∃ J : nerve (ULift.{u} ℕ) ⟶ I₀, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_diagram_of_shapeTower id monotone_id (fun k ↦ ⟨k, le_rfl⟩)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oneConeSimplexIso_prefix
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n))
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index_restrict hD₁)

/-- 奇数面と同じ右形状表示でも、元の右添字圏内の全図式を構成する。 -/
lemma exists_comparisonRightParityIndexDiagram (l₀ : s₀.right_shape ≅ (Δ[0] : SSet.{u})) :
    ∃ J : nerve (ULift.{u} ℕ) ⟶ I₁, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex n ≫ J =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_diagram_of_shapeTower id monotone_id (fun k ↦ ⟨k, le_rfl⟩)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oneConeSimplexIso_prefix
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightParityShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ l₀ n))
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index_restrict hD₁)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
