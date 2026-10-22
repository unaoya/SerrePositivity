module
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackComparison
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

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
namespace SerrePositivity.InfinityCategories

lemma functorPullbackComparisonFamily_source {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c) :
    functorPullbackComparisonFamily Q c hc ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
        (functorVertexEquiv K X).symm (pullbackCone Q).vertex :=
  arrowFamilyOfFunctorEdge_source _

lemma functorPullbackComparisonFamily_target {K X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c) :
    functorPullbackComparisonFamily Q c hc ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
        (functorVertexEquiv K X).symm c.vertex :=
  arrowFamilyOfFunctorEdge_target _

lemma functorPullbackComparison_target_pointwise {K X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c) (k : K _⦋0⦌) :
    IsLimitCone (evaluateFunctorCone c k) :=
  isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits
    (fun _ ↦ HasFiniteLimits.hasLimit _) c hc k

end SerrePositivity.InfinityCategories
