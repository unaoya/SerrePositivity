module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSequenceDiagram

/-!
概要：元の共通大域頂点上で、可算全比較の増大余錐も全図式として貼り合わせる。
方針：各全余錐を固定標的の slice へ curry し、厳密な全制限を貼合へ渡す。
規約：元の大域頂点の compact 性は要求しない。使われ方：共通部分表示の余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 比較の全増大余錐を、元の同じ大域頂点の slice 内の全図式とする。 -/
def comparisonSliceDiagram (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    (SSet.uliftFunctor.{u + 1, u}).obj s.shape ⟶ sliceOver (SSet.yonedaEquiv.symm c₀.vertex) :=
  sliceOverCurry s.augmentation.val (by
    rw [← s.vertex_left, JoinCocone.vertex_eq, Equiv.symm_apply_apply])

/-- 全展開は元の同じ全増大余錐を厳密に回収する。 -/
lemma comparisonSliceDiagram_uncurry (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    sliceOverUncurry (comparisonSliceDiagram s) = s.augmentation.val :=
  sliceOverUncurry_curry _ _

/-- 固定大域頂点の slice からの射影は元の全比較図式である。 -/
lemma comparisonSliceDiagram_projection (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    comparisonSliceDiagram s ≫ sliceOverProjection (SSet.yonedaEquiv.symm c₀.vertex) = s.diagram := by
  rw [comparisonSliceDiagram, sliceOverCurry_projection]
  exact s.augmentation.property

variable [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  [Quasicategory I₀] [IsKappaFiltered μ I₀]
  [Quasicategory I₁] [IsKappaFiltered μ I₁]
  (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
  (hD₀ : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
  (hD₁ : ∀ i : I₁ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
  (s₀ : CompactPresentationComparison μ D₀ D₁ c₀ c₁)

/-- 可算全比較の全余錐を固定大域頂点の slice 内で見ても、全制限は厳密に一致する。 -/
lemma comparisonSequenceSliceDiagram_restrict (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map
        (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) ≫
      comparisonSliceDiagram (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ (n + 1)) =
    comparisonSliceDiagram (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm c₀.vertex)
  rw [sliceOverUncurry_precomp, comparisonSliceDiagram_uncurry, comparisonSliceDiagram_uncurry]
  exact comparisonSequence_augmentation_restrict_val hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n

/-- 元の二表示の可算全比較は、同じ元の大域頂点上の native な全図式となる。 -/
lemma exists_comparisonSequenceSliceDiagram {m : ℕ} (e₀ : s₀.shape ≅ (Δ[m] : SSet.{u})) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶
        sliceOver (SSet.yonedaEquiv.symm c₀.vertex),
      ∀ n, (SSet.uliftFunctor.{u + 1, u}).map
          (sequentialNerveInitialSimplex (comparisonSequenceDegree m n)) ≫ G =
        (SSet.uliftFunctor.{u + 1, u}).map
          (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀ n).inv ≫
            comparisonSliceDiagram (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n) :=
  exists_nativeDiagram_of_shapeTower (comparisonSequenceDegree m)
    (comparisonSequenceDegree_monotone m) (comparisonSequenceDegree_cofinal m)
    (fun n ↦ (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n).shape)
    (comparisonSequenceInclusion hμ hC hc₀ hc₁ hD₀ hD₁ s₀)
    (comparisonSequenceShapeIso hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (comparisonSequenceShapeIso_prefix hμ hC hc₀ hc₁ hD₀ hD₁ s₀ e₀)
    (fun n ↦ comparisonSliceDiagram (comparisonSequence hμ hC hc₀ hc₁ hD₀ hD₁ s₀ n))
    (comparisonSequenceSliceDiagram_restrict hμ hC hc₀ hc₁ hD₀ hD₁ s₀)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
