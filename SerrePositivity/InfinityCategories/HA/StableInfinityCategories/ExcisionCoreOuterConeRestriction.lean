module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.NormalizedConeRestrictionVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreSourceComparisons
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

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

def excisionCoreOuterConeRestriction {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreDiagram ≫ F) 1 1)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedConeRestriction _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreOuterCospanBoundary
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreOuterCospanBoundary_diagram F)

lemma excisionCoreOuterConeRestriction_cone {X : SSet.{u}}
    (F : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionCorePunctured) ≫ F)) :
    (excisionCoreOuterConeRestriction F).app (Opposite.op ⦋0⦌) c =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCorePuncturedOuterCone c :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.normalizedConeRestriction_cone _ _ _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
