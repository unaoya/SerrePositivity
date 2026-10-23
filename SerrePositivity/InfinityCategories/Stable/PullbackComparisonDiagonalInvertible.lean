module
public import SerrePositivity.InfinityCategories.Stable.EquivalenceArrowLimits
public import SerrePositivity.InfinityCategories.Stable.SquareDiagonal
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeSquareReadback
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonComponentInvertible

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma functorPullbackComparison_diagonal_isInvertible {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c)
    (hQ : IsPullbackSquare (Q ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (hp : ∀ j : (horn 2 2 : SSet.{u}) _⦋0⦌,
      IsEquivalencePathVertex ((pullbackCospan Q).app (Opposite.op ⦋0⦌) j)) :
    IsInvertibleEdge (squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm
      (functorPullbackComparisonEdge Q c hc).edge))) := by
  let e := functorPullbackComparisonEdge Q c hc
  let F := uncurry (SSet.yonedaEquiv.symm e.edge)
  have hl : IsInvertibleEdge (squareLeftArrow F) :=
    (isInvertibleEdge_congr (squareLeftArrow_functorEdge_edge e)).mpr
      (functorPullbackComparison_component_isInvertible Q c hc _ hQ)
  have hv := squareTopArrow_functorEdge_vertex e
  have ht := congrArg intervalFunctorVertexEdge hv
  erw [intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply] at ht
  have hg : IsEquivalencePathVertex c.vertex :=
    isEquivalencePathVertex_limitVertex c
      (functorPullbackComparison_target_pointwise Q c hc _)
      (functorPullbackComparison_target_pointwise Q c hc _) hp
  have hr : IsInvertibleEdge (squareTopArrow F) := (isInvertibleEdge_congr ht).mpr hg
  change IsIso (Truncated.HomotopyCategory.homMk (squareDiagonalArrow F))
  rw [← squareLeftTop_homMk_diagonal]
  have : IsIso (Truncated.HomotopyCategory.homMk (squareLeftArrow F)) := hl
  have : IsIso (Truncated.HomotopyCategory.homMk (squareTopArrow F)) := hr
  infer_instance

end SerrePositivity.InfinityCategories
