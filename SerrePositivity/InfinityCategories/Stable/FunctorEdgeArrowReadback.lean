module
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeArrowFamily

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
namespace SerrePositivity.InfinityCategories

lemma arrowFamilyOfFunctorEdge_vertex_edge {K X : SSet.{u}}
    {a b : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b) (k : K _⦋0⦌) :
    intervalFunctorVertexEdge ((arrowFamilyOfFunctorEdge e).app (Opposite.op ⦋0⦌) k) =
      (e.map ((truncation 2).map (evaluateFunctorAt k))).edge := by
  rw [arrowFamilyOfFunctorEdge_vertex, intervalFunctorVertexEdge_functorVertex,
    SSet.yonedaEquiv_comp]
  rfl

end SerrePositivity.InfinityCategories
