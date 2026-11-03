module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceVertices
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue

/-!
概要：全第一辺選択の元の二実頂点の指定同型の終点像を、元の二実 prism 比較へ戻す。
方針：全 fiber 評価の curry と、同じ可縮延長空間の指定比較の像を使う。
規約：元の二実頂点と指定比較を保持。使われ方：第一辺比較の最後辺輸送への同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二実第一辺の指定頂点比較の全終点像は、同じ二実 prism の指定 fiber 比較。 -/
lemma coherentColimitRawFirstChoiceEndpoint_comparison_heq (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : SSet.Homotopy F G) {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (W₀ W₁ : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hp₀ : W₀ ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
    (hp₁ : W₁ ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
    (hs₀ : prismEndpoint 0 K ≫ W₀ = f ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (hs₁ : prismEndpoint 0 K ≫ W₁ = f ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (g₀ g₁ : K ⟶ vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hj₀ : prismEndpoint 1 K ≫ W₀ = g₀ ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)))
    (hj₁ : prismEndpoint 1 K ≫ W₁ = g₁ ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G))) :
    HEq (VertexIso.map ((coherentColimitRawFirstChoiceSpace_isContractibleKan B a f).vertexIso
      (coherentColimitRawFirstChoiceVertex B a f W₀ hp₀ hs₀)
      (coherentColimitRawFirstChoiceVertex B a f W₁ hp₁ hs₁))
      (curry (coherentColimitRawFirstChoiceEndpoint B a f)))
      (relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection
        (fst (Δ[1] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
        (prismEndpoint 0 K) (prismEndpoint_zero_leftAnodyne K)
        (f ≫ vertexFiberι pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
        (coherentColimitRawFirstChoice_initial_base B a f) (prismEndpoint 1 K) _
        (coherentColimitRawFirstChoice_final_base B a f)
        W₀ W₁ hp₀ hp₁ hs₀ hs₁ g₀ g₁ hj₀ hj₁) := by
  rw [coherentColimitRawFirstChoiceEndpoint, relativeExtensionUniversalPrismEndpoint,
    MonoidalClosed.curry_uncurry]
  exact (relativeExtensionFiberEndpoint_witnessIso_heq_map pointedSpaceProjection _ _
    (prismEndpoint_zero_leftAnodyne K) _ _ _ _ _
    W₀ W₁ hp₀ hp₁ hs₀ hs₁ g₀ g₁ hj₀ hj₁).symm

end SerrePositivity.InfinityCategories.F2
