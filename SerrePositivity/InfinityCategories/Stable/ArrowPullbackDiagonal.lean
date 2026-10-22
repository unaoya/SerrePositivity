module
public import SerrePositivity.InfinityCategories.Stable.LimitConeDiagonalVertex
public import SerrePositivity.InfinityCategories.Stable.ConeSquareInitialVertex
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonComponentInvertible

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma exists_arrowPullbackSquare_diagonal {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c)
    (hQ : IsPullbackSquare (Q ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      pullbackCospan R = pullbackCospan Q ∧ IsPullbackSquare R ∧
      squareVertex R 0 0 = functorVertex (SSet.yonedaEquiv.symm
        (squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm
          (functorPullbackComparisonEdge Q c hc).edge))).edge) := by
  have he := functorPullbackComparison_component_isInvertible Q c hc
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) hQ
  obtain ⟨d, hd, hv⟩ := exists_limitCone_vertex_diagonal c hc
    (functorPullbackComparisonEdge Q c hc) he
  exact ⟨coneSquare d, coneSquare_cospan d, coneSquare_isPullback d hd,
    (coneSquare_initialVertex d).trans hv⟩

end SerrePositivity.InfinityCategories
