module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceArrowLimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareDiagonal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeSquareReadback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackComparisonComponentInvertible

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma functorPullbackComparison_diagonal_isInvertible {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (hp : ∀ j : (horn 2 2 : SSet.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q).app (Opposite.op ⦋0⦌) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge Q c hc).edge))) := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge Q c hc
  let F := uncurry (SSet.yonedaEquiv.symm e.edge)
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow F) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_functorEdge_edge e)).mpr
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparison_component_isInvertible Q c hc _ hQ)
  have hv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_functorEdge_vertex e
  have ht := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge hv
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply] at ht
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex c.vertex :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isEquivalencePathVertex_limitVertex c
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparison_target_pointwise Q c hc _)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparison_target_pointwise Q c hc _) hp
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow F) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr ht).mpr hg
  change IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagonalArrow F))
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftTop_homMk_diagonal]
  have : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow F)) := hl
  have : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow F)) := hr
  infer_instance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
