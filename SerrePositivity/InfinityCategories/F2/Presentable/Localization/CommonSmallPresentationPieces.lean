module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SeedBoundedTwoPresentationComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CofinalPresentationColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverSmallColimits

/-!
概要：二表示の共通全比較から、種集合を含む小部分表示の余極限を比較する。
方針：同じ実頂点列の部分 poset への共終性を使い、対象上の圏で余極限を取る。
規約：比較は元の共通大域頂点の上で行う。使われ方：HTT 5.5.4.13 の小部分表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 全比較の両実頂点列による小部分表示は、元の共通頂点の上で同型な余極限を持つ。 -/
lemma exists_commonSmallPresentation_colimits
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁} {hv : c₀.vertex = c₁.vertex}
    {seed₀ : Set A₀} {seed₁ : Set A₁}
    (hC : HasSmallColimits C)
    (s : SeedBoundedTwoPresentationComparison c₀ c₁ hv seed₀ seed₁) :
    let E₀ := (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialPieceInclusionFunctor seed₀ (nerveIndexSequence s.leftIndex))) ≫
        coconeSliceDiagram c₀
    let E₁ := (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (sequentialPieceInclusionFunctor seed₁ (nerveIndexSequence s.rightIndex))) ≫
        transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm
    ∃ a₀ : JoinCocone E₀, ∃ a₁ : JoinCocone E₁,
      IsColimitCone a₀ ∧ IsColimitCone a₁ ∧ Nonempty (VertexIso a₀.vertex a₁.vertex) := by
  dsimp only
  let X := sliceOver (SSet.yonedaEquiv.symm c₀.vertex)
  have hX : HasSmallColimits X := sliceOver_hasSmallColimits hC _
  let r₀ := nerveMap (nerveIndexPieceMonotone seed₀ s.leftIndex).functor
  let r₁ := nerveMap (nerveIndexPieceMonotone seed₁ s.rightIndex).functor
  let E₀ := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (sequentialPieceInclusionFunctor seed₀ (nerveIndexSequence s.leftIndex))) ≫
      coconeSliceDiagram c₀
  let E₁ := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (sequentialPieceInclusionFunctor seed₁ (nerveIndexSequence s.rightIndex))) ≫
      transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm
  obtain ⟨a₀, ha₀⟩ := hX _ E₀
  obtain ⟨a₁, ha₁⟩ := hX _ E₁
  refine ⟨a₀, a₁, ha₀, ha₁, ?_⟩
  apply nonempty_twoCofinalPresentation_colimitIso hX r₀
    (nerveIndexPiece_nerve_isRightCofinal seed₀ s.leftIndex s.left_seed) r₁
    (nerveIndexPiece_nerve_isRightCofinal seed₁ s.rightIndex s.right_seed)
    E₀ E₁ s.diagram ?_ ?_ a₀ ha₀ a₁ ha₁
  · dsimp only [E₀, r₀]
    rw [← Category.assoc, ← Functor.map_comp, nerveIndexPiece_factorization]
    exact s.left_eq
  · dsimp only [E₁, r₁]
    rw [← Category.assoc, ← Functor.map_comp, nerveIndexPiece_factorization]
    exact s.right_eq

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
