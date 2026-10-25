module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CommonSmallPresentationPieces

/-!
概要：元の二つの compact filtered 表示から、共通頂点上の小部分表示を構成する。
方針：種集合を支配する全比較に、部分 poset の小ささと共終余極限比較を適用する。
規約：大域頂点の compact 性を要求しない。使われ方：三角形表示の同時細分。
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

/-- 元の種集合を含む小さい filtered 部分表示と、共通大域頂点上の余極限同型。 -/
structure SmallPresentationComparison (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁) (hv : c₀.vertex = c₁.vertex)
    (seed₀ : Set A₀) (seed₁ : Set A₁) where
  leftPiece : Set A₀
  rightPiece : Set A₁
  left_seed : seed₀ ⊆ leftPiece
  right_seed : seed₁ ⊆ rightPiece
  left_small : HasCardinalLT leftPiece μ
  right_small : HasCardinalLT rightPiece μ
  left_filtered : IsFiltered leftPiece
  right_filtered : IsFiltered rightPiece
  leftCocone : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (subsetInclusion leftPiece)) ≫ coconeSliceDiagram c₀)
  rightCocone : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (subsetInclusion rightPiece)) ≫
      transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm)
  left_colimit : IsColimitCone leftCocone
  right_colimit : IsColimitCone rightCocone
  comparison : VertexIso leftCocone.vertex rightCocone.vertex

/-- 原典の二表示から、任意の小さい種集合を含む比較可能な小部分表示が存在する。 -/
lemma nonempty_smallPresentationComparison
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁] [IsCardinalFiltered A₀ μ] [IsCardinalFiltered A₁ μ]
    [IsKappaFiltered μ (nerve A₀)] [IsKappaFiltered μ (nerve A₁)]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C)
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁)
    (hC : HasSmallColimits C) (hc₀ : IsColimitCone c₀) (hc₁ : IsColimitCone c₁)
    (hD₀ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hD₁ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up i)))
    (hv : c₀.vertex = c₁.vertex)
    (seed₀ : Set A₀) (hs₀ : HasCardinalLT seed₀ μ)
    (seed₁ : Set A₁) (hs₁ : HasCardinalLT seed₁ μ) :
    Nonempty (SmallPresentationComparison μ c₀ c₁ hv seed₀ seed₁) := by
  obtain ⟨s⟩ := nonempty_seedBoundedTwoPresentationComparison hμ D₀ D₁ c₀ c₁
    hC hc₀ hc₁ hD₀ hD₁ hv seed₀ hs₀ seed₁ hs₁
  obtain ⟨a₀, a₁, ha₀, ha₁, e⟩ := exists_commonSmallPresentation_colimits hC s
  refine ⟨⟨sequentialPiece seed₀ (nerveIndexSequence s.leftIndex),
    sequentialPiece seed₁ (nerveIndexSequence s.rightIndex),
    seed_subset_sequentialPiece _ _, seed_subset_sequentialPiece _ _,
    sequentialPiece_hasCardinalLT hμ seed₀ hs₀ _,
    sequentialPiece_hasCardinalLT hμ seed₁ hs₁ _,
    sequentialPiece_isFiltered seed₀ (nerveIndexSequence_monotone s.leftIndex) s.left_seed,
    sequentialPiece_isFiltered seed₁ (nerveIndexSequence_monotone s.rightIndex) s.right_seed,
    a₀, a₁, ha₀, ha₁, e.some⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
