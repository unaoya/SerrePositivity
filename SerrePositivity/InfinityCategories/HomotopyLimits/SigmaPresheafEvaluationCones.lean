module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FlippedConeEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafInfinity
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion

/-!
概要：P_Σ の元の族と元の有限離散極限錐から、元の評価関手族の実際の極限錐を構成する。
方針：二変数評価を交換し、各前層の元の有限積保存を同じ全評価錐へ適用する。
規約：元の全錐・族・頂点・脚を保持。元の錐の極限性だけを入力する。
使われ方：P_Σ の sifted 閉性の比較元の全錐の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)

/-- 元の P_Σ の族の二変数評価を交換した、元の対象ごとの評価関手族。 -/
def sigmaPresheafFamilyFlip : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} :=
  internalHomFlipHomEquiv _ _ _ (r ≫ sigmaPresheafInfinityInclusion C)

/-- 元の P_Σ の族を、元の反変定義域の指定頂点で評価する。 -/
def sigmaPresheafVertexEvaluation
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  (r ≫ sigmaPresheafInfinityInclusion C) ≫ evaluateFunctorAt x

/-- 元の有限離散錐の全体を二変数評価で写した、元の関手圏内の全錐。 -/
def sigmaPresheafEvaluationCone {J : Type u} {p : nerve (Discrete J) ⟶ C.op}
    (c : JoinCone p) : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map p ≫
      sigmaPresheafFamilyFlip r) :=
  mapJoinCone (sigmaPresheafFamilyFlip r) (JoinCone.ulift.{u, u + 1} c)

/-- 元の P_Σ の条件から、同じ元の評価全錐が各点で極限錐になる。 -/
lemma sigmaPresheafEvaluationCone_isPointwiseLimit {J : Type u} [Finite J]
    {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p) (hc : IsLimitCone c) :
    IsPointwiseLimitCone (sigmaPresheafEvaluationCone r c) := by
  apply flippedCone_isPointwiseLimit_of_maps (r ≫ sigmaPresheafInfinityInclusion C)
    (JoinCone.ulift.{u, u + 1} c)
  intro b
  have hF : PreservesFiniteProductsFromSmallSource
      ((functorVertexEquiv _ _).symm ((r ≫ sigmaPresheafInfinityInclusion C).app
        (Opposite.op ⦋0⦌) b)) := sigmaPresheafInfinity_vertex (r.app (Opposite.op ⦋0⦌) b)
  exact hF.map_isLimit hc

/-- 元の P_Σ の族で評価した元の有限極限錐は、元の関手圏でも極限錐。 -/
lemma sigmaPresheafEvaluationCone_isLimit {J : Type u} [Finite J]
    {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (sigmaPresheafEvaluationCone r c) :=
  isLimitCone_of_pointwise _ (sigmaPresheafEvaluationCone_isPointwiseLimit r c hc)

/-- 元の評価全錐の頂点は、元の持ち上げた頂点での評価関手そのもの。 -/
lemma sigmaPresheafEvaluationCone_vertex {J : Type u} {p : nerve (Discrete J) ⟶ C.op}
    (c : JoinCone p) : (sigmaPresheafEvaluationCone r c).vertex =
      functorVertex (sigmaPresheafVertexEvaluation r (JoinCone.ulift.{u, u + 1} c).vertex) := by
  rw [sigmaPresheafEvaluationCone, mapJoinCone_vertex]
  exact internalHomFlipHomEquiv_app_zero (r ≫ sigmaPresheafInfinityInclusion C) _

end SerrePositivity.InfinityCategories.HomotopyLimits
