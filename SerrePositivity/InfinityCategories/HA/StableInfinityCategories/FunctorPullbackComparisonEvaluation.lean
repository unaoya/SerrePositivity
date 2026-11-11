module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorPullbackComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence

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

lemma functorPullbackComparisonFamily_source {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonFamily Q c hc ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q).vertex :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_source _

lemma functorPullbackComparisonFamily_target {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorPullbackComparisonFamily Q c hc ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm c.vertex :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowFamilyOfFunctorEdge_target _

lemma functorPullbackComparison_target_pointwise {K X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan Q)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCone c k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits
    (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit _) c hc k

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
