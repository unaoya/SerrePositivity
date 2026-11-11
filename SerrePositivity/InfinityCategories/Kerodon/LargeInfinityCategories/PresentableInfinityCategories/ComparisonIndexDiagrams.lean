module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonIndexShapes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallShapeTowerGluing

/-!
概要：可算全比較の両側の添字を、元の各小さい添字圏内の全可算図式へ貼り合わせる。
方針：各側の一段ずつの標準単体表示と元の全添字の制限等式を使う。
規約：元の filtered 表示の添字圏を保つ。使われ方：共通部分表示の添字列。

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

/-- 左側の元の添字図式は、元の小さい添字圏内の一つの全可算図式になる。 -/
lemma exists_comparisonLeftIndexDiagram {m : ℕ}
    (e₀ : s₀.left_shape ≅ (Δ[m] : SSet.{u})) :
    ∃ J : nerve (ULift.{u} ℕ) ⟶ I₀, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (m + n) ≫ J =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_diagram_of_shapeTower (fun n ↦ m + n)
    (fun _ _ h ↦ Nat.add_le_add_left h m) (fun k ↦ ⟨k, by omega⟩)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_shape Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceLeftShapeIso_prefix hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).left_index_restrict hD₁)

/-- 右側についても、元の小さい添字圏内で全可算図式が構成できる。 -/
lemma exists_comparisonRightIndexDiagram {m : ℕ}
    (e₀ : s₀.right_shape ≅ (Δ[m] : SSet.{u})) :
    ∃ J : nerve (ULift.{u} ℕ) ⟶ I₁, ∀ n,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (m + n) ≫ J =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_diagram_of_shapeTower (fun n ↦ m + n)
    (fun _ _ h ↦ Nat.add_le_add_left h m) (fun k ↦ ⟨k, by omega⟩)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_shape Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRightShapeIso_prefix hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceRound hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).right_index_restrict hD₁)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
