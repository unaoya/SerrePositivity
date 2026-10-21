module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafColimitLegConjugate
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafOriginalLegComparison

/-!
概要：実際の前層余錐脚の底変換を、元の有限評価錐の指定脚変換そのものへ照合する。
方針：両者の同じ native 脚の全一単体と、元の評価関手の端点を使う。
規約：元の族・指定余錐・元の脚を保持し、有限性や底の充填性を要求しない。
使われ方：実際の頂点脚の共役を、標準の有限評価余極限錐の Kan 脚と同定する。
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
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  {J : Type u} {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p) (j : J)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "k" => ULift.up (nerveVertex (Discrete.mk j))
local notation "x₁" => NatTrans.app (CategoryTheory.Functor.map SSet.uliftFunctor p)
  (Opposite.op ⦋0⦌) k
local notation "q₀" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₀) q
local notation "q₁" => F1B.kanPostcomposeCocone (evaluateFunctorAt x₁) q

/-- 元の全余錐脚の底辺を、元の有限評価関手の端点表示で保持する。 -/
def sigmaPresheafCoconeBottomLeg :
    SSet.Edge (functorVertex (sigmaPresheafVertexEvaluation r x₀))
      (functorVertex (sigmaPresheafFiniteEvaluationFamily r (p := p) j)) :=
  coconeWholeEdgeBottom q₀ q₁ (presheafCoconeImageLeg q c k).toTruncated

/-- 両端を揃えた底辺と元の評価脚変換は、同じ全一単体。 -/
lemma sigmaPresheafCoconeBottomLeg_edge :
    (sigmaPresheafCoconeBottomLeg r q c j).edge =
      (intervalMappingEdgeOfVertex (sigmaPresheafConeLegTransformation r c j)).edge := by
  exact (presheafCoconeImageLeg_bottom q c k).trans
    (sigmaPresheafConeLegTransformation_edge r c j).symm

/-- 元の全余錐脚の底辺は、元の同じ評価脚変換から回収した辺そのもの。 -/
lemma sigmaPresheafCoconeBottomLeg_eq :
    sigmaPresheafCoconeBottomLeg r q c j =
      intervalMappingEdgeOfVertex (sigmaPresheafConeLegTransformation r c j) :=
  SSet.Edge.ext (sigmaPresheafCoconeBottomLeg_edge r q c j)

/-- 底辺の変換頂点は、元の評価脚の指定変換そのもの。 -/
lemma sigmaPresheafCoconeBottomLeg_vertex :
    intervalMappingVertexOfEdge (sigmaPresheafCoconeBottomLeg r q c j) =
      sigmaPresheafConeLegTransformation r c j := by
  rw [sigmaPresheafCoconeBottomLeg_eq]
  exact (intervalMappingEdgeVertexEquiv _ _).apply_symm_apply _

end SerrePositivity.InfinityCategories.HomotopyLimits
