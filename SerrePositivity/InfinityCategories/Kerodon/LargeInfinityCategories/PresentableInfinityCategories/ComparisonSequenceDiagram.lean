module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSequenceSimplexShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeShapeTowerGluing

/-!
概要：元の二表示の可算全比較列を、native な全可算図式へ実際に貼り合わせる。
方針：構成済みの全形状同型・指定包含・全図式の等式を公開貼合入口へ渡す。
規約：元の全有限段を厳密に回収する。使われ方：両表示の共通小部分図式の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 元の二表示から構成した可算比較列は、全有限段を保つ一つの native 図式となる。 -/
lemma exists_comparisonSequenceDiagram
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    {I₀ I₁ : SSet.{u}} [Quasicategory I₀] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₀]
    [Quasicategory I₁] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hc₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₀) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i : I₁ _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    {m : ℕ} (e₀ : s₀.shape ≅ (Δ[m] : SSet.{u})) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C,
      ∀ n, (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m n)) ≫ G =
        (SSet.uliftFunctor.{u + 1, u}).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_nativeDiagram_of_shapeTower (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree_monotone m) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceDegree_cofinal m)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequenceShapeIso_prefix hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSequence_diagram_restrict hμ hC hc₀ hc₁ hD₀ hD₁ s₀)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
