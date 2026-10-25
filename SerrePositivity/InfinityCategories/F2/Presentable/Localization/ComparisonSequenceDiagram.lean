module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSequenceSimplexShape
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.NativeShapeTowerGluing

/-!
概要：元の二表示の可算全比較列を、native な全可算図式へ実際に貼り合わせる。
方針：構成済みの全形状同型・指定包含・全図式の等式を公開貼合入口へ渡す。
規約：元の全有限段を厳密に回収する。使われ方：両表示の共通小部分図式の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 元の二表示から構成した可算比較列は、全有限段を保つ一つの native 図式となる。 -/
lemma exists_comparisonSequenceDiagram
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    {I₀ I₁ : SSet.{u}} [Quasicategory I₀] [IsKappaFiltered μ I₀]
    [Quasicategory I₁] [IsKappaFiltered μ I₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}
    (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (s₀ : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    {m : ℕ} (e₀ : s₀.shape ≅ (Δ[m] : SSet.{u})) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C,
      ∀ n, (SSet.uliftFunctor.{u + 1, u}).map
          (sequentialNerveInitialSimplex (comparisonSequenceDegree m n)) ≫ G =
        (SSet.uliftFunctor.{u + 1, u}).map
          (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
            (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram :=
  exists_nativeDiagram_of_shapeTower (comparisonSequenceDegree m)
    (comparisonSequenceDegree_monotone m) (comparisonSequenceDegree_cofinal m)
    (fun n ↦ (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape)
    (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀)
    (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (comparisonSequenceShapeIso_prefix hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).diagram)
    (comparisonSequence_diagram_restrict hμ hC hc₀ hc₁ hD₀ hD₁ s₀)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
