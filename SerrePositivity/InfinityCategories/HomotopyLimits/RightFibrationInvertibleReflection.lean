module

public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp

/-!
概要：右ファイブレーションは元の辺の可逆性を反映する。
方針：同じ辺を反転し、元の left fibration の反映定理を適用する。
規約：元の全空間と底の quasicategory 性を要求する。
使われ方：元の極限錐への比較辺を、その元の頂点辺から検出する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 右ファイブレーションの元の辺は、元の底への像が可逆なら可逆。 -/
lemma rightFibration_reflects_isInvertibleEdge {E B : SSet.{u}} [Quasicategory E]
    [Quasicategory B] (p : E ⟶ B) [RightFibration p] {a b : E _⦋0⦌}
    (e : SSet.Edge a b) (he : IsInvertibleEdge (e.map p)) : IsInvertibleEdge e := by
  apply (isInvertibleEdge_op_iff e.toTruncated).mp
  have hmap : (edgeOp e.toTruncated).map ((truncation 2).map (SSet.opFunctor.map p)) =
      edgeOp (e.map p).toTruncated := by
    apply SSet.Truncated.Edge.ext
    rfl
  apply leftFibration_reflects_invertibleEdge (SSet.opFunctor.map p) (edgeOp e.toTruncated)
  rw [hmap]
  exact he.op

end SerrePositivity.InfinityCategories.HomotopyLimits
