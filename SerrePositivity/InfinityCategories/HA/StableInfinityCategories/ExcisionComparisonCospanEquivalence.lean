module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionRawParameterRestriction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionPullbackComparisonFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeArrowReadback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackComparisonComponentInvertible

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionComparison_cospan_isEquivalencePath {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] {F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured) ≫ F))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))
    (j : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionPullbackComparisonFamily c d hd)).app
      (Opposite.op ⦋0⦌) j) := by
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary.app (Opposite.op ⦋0⦌) j
  have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare_replaced_evaluate_cospan c j]
    exact hF k
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparison_component_isInvertible
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c)) d hd k hQ
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_vertex_edge
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionRawSuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionReplaceInitial c))
      d hd) k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mpr he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
