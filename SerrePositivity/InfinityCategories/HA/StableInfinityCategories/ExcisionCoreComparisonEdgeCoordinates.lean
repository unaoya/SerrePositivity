module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TruncatedEdgeTransport

/-!
概要：実 θ と元の始点の比較辺の合成を、同じ錐の圏で照合する。
方針：正規化した制限と全三辺を保持する実二単体を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第一合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open SimplicialObject.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCoreComparisonEdge_edge {X : SSet.{u}} [Quasicategory X]
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone e) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge F d hd e he).edge =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonConeEdge F d hd e he).map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1))))).edge := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreComparisonEdge]
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.truncatedEdge_cast_edge
  · exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone_vertex _).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedLimitCone_vertex F d hd)
  · rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
