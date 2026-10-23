module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackVertexData
public import SerrePositivity.InfinityCategories.Core.PullbackSimplex

/-!
概要：二対象と指定矢印の三つ組から lax pullback の頂点を作る。
方針：矢印を関手の頂点へ戻し引き戻しの零単体に持ち上げる。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二対象と指定矢印の三つ組から lax pullback の頂点を作る。
方針：矢印を関手の頂点へ戻し引き戻しの零単体に持ち上げる。
規約：元の対象と一次単体を保持し、同値類へ移さない。
使われ方：Tamme Remark 6 の対象と対象間写像空間。 -/
def laxPullbackVertexOfData {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (x : LaxPullbackVertexData p q) : (laxPullback p q) _⦋0⦌ :=
  pullbackSimplex (arrowEndpointPair C) (p ⊗ₘ q)
    ((intervalFunctorVertexEdgeEquiv C).symm x.arrow) (x.left, x.right) (by
      apply Prod.ext
      · exact (intervalFunctorVertexTypedEdge _).src_eq.symm.trans
          ((congrArg (C.δ 1) ((intervalFunctorVertexEdgeEquiv C).apply_symm_apply x.arrow)).trans
            x.source)
      · exact (intervalFunctorVertexTypedEdge _).tgt_eq.symm.trans
          ((congrArg (C.δ 0) ((intervalFunctorVertexEdgeEquiv C).apply_symm_apply x.arrow)).trans
            x.target))

end SerrePositivity.InfinityCategories.F2
