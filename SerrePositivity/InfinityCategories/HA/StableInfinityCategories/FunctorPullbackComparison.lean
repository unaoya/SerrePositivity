module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorEdgeArrowFamily

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def functorPullbackConeComparisonEdge {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q) c :=
  Classical.choice (hc.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q))

def functorPullbackComparisonEdge {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q).vertex c.vertex :=
  (functorPullbackConeComparisonEdge Q c hc).map
    ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)))

def functorPullbackComparisonFamily {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    K ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge (functorPullbackComparisonEdge Q c hc)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
